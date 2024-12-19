{-# LANGUAGE RecordWildCards  #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant variable capture" #-}
--
-- INFOB3CC Concurrency
-- Practical 2: Single Source Shortest Path
--
--    Δ-stepping: A parallelisable shortest path algorithm
--    https://www.sciencedirect.com/science/article/pii/S0196677403000762
--
-- https://ics.uu.nl/docs/vakken/b3cc/assessment.html
--
-- https://cs.iupui.edu/~fgsong/LearnHPC/sssp/deltaStep.html
--

module DeltaStepping (

  Graph, Node, Distance,
  deltaStepping,

) where

import Control.Concurrent
import Control.Monad
import Data.Graph.Inductive                                         ( Gr )
import Data.IORef
import Data.IntMap.Strict                                           ( IntMap )
import Data.IntSet                                                  ( IntSet )
import Data.Vector.Storable                                         ( Vector )
import Text.Printf
import qualified Data.Graph.Inductive                               as G
import qualified Data.IntMap.Strict                                 as Map
import qualified Data.IntSet                                        as Set
import qualified Data.Vector.Mutable                                as V
import qualified Data.Vector.Storable                               as M ( unsafeFreeze )
import qualified Data.Vector.Storable.Mutable                       as M
import Data.Maybe (isNothing, fromJust, isJust)
import Data.Foldable (foldlM)


type Graph    = Gr String Distance  -- Graphs have nodes labelled with Strings and edges labelled with their distance
type Node     = Int                 -- Nodes (vertices) in the graph are integers in the range [0..]
type Distance = Float               -- Distances between nodes are (positive) floating point values


-- | Find the length of the shortest path from the given node to all other nodes
-- in the graph. If the destination is not reachable from the starting node the
-- distance is 'Infinity'.
--
-- Nodes must be numbered [0..]
--
-- Negative edge weights are not supported.
--
-- NOTE: The type of the 'deltaStepping' function should not change (since that
-- is what the test suite expects), but you are free to change the types of all
-- other functions and data structures in this module as you require.
--
deltaStepping
    :: Bool                             -- Whether to print intermediate states to the console, for debugging purposes
    -> Graph                            -- graph to analyse
    -> Distance                         -- delta (step width, bucket width)
    -> Node                             -- index of the starting node
    -> IO (Vector Distance)
deltaStepping verbose graph delta source = do
  threadCount <- getNumCapabilities             -- the number of (kernel) threads to use: the 'x' in '+RTS -Nx'

  -- Initialise the algorithm
  (buckets, distances)  <- initialise graph delta source
  printVerbose verbose "initialse" graph delta buckets distances

  let
    -- The algorithm loops while there are still non-empty buckets
    loop = do
      done <- allBucketsEmpty buckets
      if done
      then return ()
      else do
        printVerbose verbose "result" graph delta buckets distances
        step verbose threadCount graph delta buckets distances
        loop
  loop

  printVerbose verbose "result" graph delta buckets distances
  -- Once the tentative distances are finalised, convert into an immutable array
  -- to prevent further updates. It is safe to use this "unsafe" function here
  -- because the mutable vector will not be used any more, so referential
  -- transparency is preserved for the frozen immutable vector.
  --
  -- NOTE: The function 'Data.Vector.convert' can be used to translate between
  -- different (compatible) vector types (e.g. boxed to storable)
  --
  M.unsafeFreeze distances

-- Initialise algorithm state
--
initialise
    :: Graph
    -> Distance
    -> Node
    -> IO (Buckets, TentativeDistances)
initialise graph delta source = do
  let amountOfNodes = length $ G.nodes graph
  tentatives <- M.replicate amountOfNodes infinity

  let lEdges = G.labEdges graph
  let maximumDistance = maximum (map (\(_, _, distance) -> distance) lEdges) -- find longest edge
  bucketVector <- V.replicate (max 1 $ ceiling $ maximumDistance / delta) Set.empty

  firstBucketIORef <- newIORef 0
  let buckets = Buckets {firstBucket = firstBucketIORef, bucketArray = bucketVector}
  relax buckets tentatives delta (source, 0)

  return (buckets, tentatives)


-- Take a single step of the algorithm.
-- That is, one iteration of the outer while loop.

step
    :: Bool
    -> Int
    -> Graph
    -> Distance
    -> Buckets
    -> TentativeDistances
    -> IO ()
step verbose threadCount graph delta buckets distances = do
  -- In this function, you need to implement the body of the outer while loop,
  -- which contains another while loop.
  -- See function 'deltaStepping' for inspiration on implementing a while loop
  -- in a functional language.
  -- For debugging purposes, you may want to place:
  --   printVerbose verbose "inner step" graph delta buckets distances
  -- in the inner loop.

  -- handle retrieving and updating the bucket index and the real index
  bucketIndex <- findNextBucket buckets
  writeIORef (firstBucket buckets) bucketIndex

  let bucketVector = bucketArray buckets
  let realIndex = bucketIndex `mod` V.length bucketVector

  -- create MVars for remembering
  visited <- newIORef Set.empty

  -- inner loop
  let
    loop = do
      printVerbose verbose "inner loop" graph delta buckets distances
      currentBucket <- V.read bucketVector realIndex
      if Set.null currentBucket then return ()
      else do
        reqs <- newMVar Map.empty

        -- divide bucket equally
        let bucketRanges = getRangesFromSet currentBucket

        -- create requests for light edges in parallel
        forkThreads threadCount $
          addRequests (<delta) graph currentBucket bucketRanges distances reqs

        -- read the results
        requests <- readMVar reqs

        -- remember which nodes have been in the current bucket
        visited' <- readIORef visited
        let newSet = Set.union visited' currentBucket
        writeIORef visited newSet

        -- make the current bucket empty
        V.write bucketVector realIndex Set.empty

        -- should happen in parallel
        relaxRequests buckets distances delta requests

        loop
  loop

  reqs <- newMVar Map.empty
  -- create requests for heavy edges in parallel
  visited' <- readIORef visited
  let ranges = getRangesFromSet visited'
  forkThreads threadCount $
    addRequests (>=delta) graph visited' ranges distances reqs

  requests <- readMVar reqs
  relaxRequests buckets distances delta requests
  where
    -- divide a set into equal pieces
    getRangesFromSet :: IntSet -> [Range]
    getRangesFromSet set = getEqualRanges threadCount (0, Set.size set - 1)


-- Once all buckets are empty, the tentative distances are finalised and the
-- algorithm terminates.
--
allBucketsEmpty :: Buckets -> IO Bool
allBucketsEmpty buckets = do
  let
    loop index = do
      let vector = bucketArray buckets
      maybeSet <- V.readMaybe vector index

      if isNothing maybeSet then return True -- if value is nothing it means we went out of range and there are only empty buckets
      else do
        let value = fromJust maybeSet
        if not (Set.null value) then return False -- if there is a set that is not empty immediately return False
        else do loop (index + 1)
  loop 0


-- Return the index of the smallest non-empty bucket. Assumes that there is at
-- least one non-empty bucket remaining.
--
findNextBucket :: Buckets -> IO Int
findNextBucket buckets = do
  let
    loop :: Int -> IO Int
    loop bucketIndex = do
      let bucketVector = bucketArray buckets
      let size = V.length bucketVector
      let realIndex = bucketIndex `mod` size

      maybeSet <- V.readMaybe bucketVector realIndex
      let set = fromJust maybeSet
      if Set.null set then do
        loop (bucketIndex + 1)
      else return bucketIndex

  firstBuck <- readIORef (firstBucket buckets)
  loop firstBuck


type Range = (Int, Int)

rangeLength :: Range -> Int
rangeLength (a, b) = b - a + 1

dropNFromRange :: Int -> Range -> Range
dropNFromRange n (a, b) = (a + n, b)

getEqualRanges :: Int -> Range -> [Range]
getEqualRanges amountOfRanges range@(a, _) = f amountOfRanges range a where
  f 1 r acc = [(acc, acc + rangeLength r - 1)]
  f n r acc = let len = rangeLength r `div` n in
    (acc, acc + len - 1) : f (n - 1) (dropNFromRange len r) (acc + len)


addRequests
    :: (Distance -> Bool)
    -> Graph
    -> IntSet
    -> [Range]
    -> TentativeDistances
    -> MVar (IntMap Distance)
    -> Int
    -> IO ()
addRequests p graph v' bucketSlices distances mapRef threadIndex = do
  let bucketSlice = bucketSlices !! threadIndex
  newRequests <- findRequests p graph v' bucketSlice distances

  -- critical section, write to shared variable
  current <- takeMVar mapRef
  putMVar mapRef (Map.union current newRequests)
  -- end of critical section


-- Create requests of (node, distance) pairs that fulfil the given predicate
--
findRequests
    :: (Distance -> Bool)
    -> Graph
    -> IntSet
    -> Range
    -> TentativeDistances
    -> IO (IntMap Distance)
findRequests p graph v' bucketSlice distances = do
  let requestsIO = map handleNode [fst bucketSlice .. snd bucketSlice] -- for each node make a map of requests
  requests <- sequence requestsIO
  return $ foldr (Map.unionWith min) Map.empty requests -- combine all the requests
  where
    handleNode :: Int -> IO (IntMap Distance)
    handleNode index = do
      foldlM addToMap Map.empty validNeighbours
      where
        node :: Node -- Node is alias for int
        node = Set.elems v' !! index

        neighbours :: [(Node, Distance)]
        neighbours = G.lsuc graph node

        validNeighbours :: [(Node, Distance)]
        validNeighbours = filter (p.snd) neighbours

        addToMap :: IntMap Distance -> (Node, Distance) -> IO (IntMap Distance)
        addToMap oldMap (neighbour, distance) = do
          tentative <- M.read distances node
          let newDistance = tentative + distance
          let oldDistance = (Map.!?) oldMap neighbour
          if isJust oldDistance && fromJust oldDistance <= newDistance
            then return oldMap
            else return $ Map.insert neighbour newDistance oldMap


-- Execute requests for each of the given (node, distance) pairs
--
relaxRequests
    :: Buckets
    -> TentativeDistances
    -> Distance
    -> IntMap Distance
    -> IO ()
relaxRequests buckets distances delta req = do
  let elems = Map.elems req
  let keys = Map.keys req
  let requests = zip keys elems
  mapM_ (relax buckets distances delta) requests -- should be parrallelisjklzed


-- Execute a single relaxation, moving the given node to the appropriate bucket
-- as necessary
--
relax :: Buckets
      -> TentativeDistances
      -> Distance
      -> (Node, Distance) -- (w, x) in the paper
      -> IO ()
relax buckets distances delta (node, newDistance) = do
   tent <- M.read distances node
   when (newDistance < tent) (
    do
      let size = V.length $ bucketArray buckets
      -- remove from old bucket
      let remIndex = floor (tent / delta) `mod` size
      oldBucket <- V.read (bucketArray buckets) remIndex
      V.write (bucketArray buckets) remIndex (Set.delete node oldBucket)

      -- insert into new bucket
      let addIndex = floor (newDistance / delta) `mod` size
      newBucket <- V.read (bucketArray buckets) addIndex
      V.write (bucketArray buckets) addIndex (Set.insert node newBucket)

      M.write distances node newDistance
    )

-- add locking 




-- -----------------------------------------------------------------------------
-- Starting framework
-- -----------------------------------------------------------------------------
--
-- Here are a collection of (data)types and utility functions that you can use.
-- You are free to change these as necessary.
--

type TentativeDistances = M.IOVector Distance

data Buckets = Buckets
  { firstBucket   :: {-# UNPACK #-} !(IORef Int)           -- real index of the first bucket (j)
  , bucketArray   :: {-# UNPACK #-} !(V.IOVector IntSet)   -- cyclic array of buckets
  }


-- The initial tentative distance, or the distance to unreachable nodes
--
infinity :: Distance
infinity = 1/0


-- Forks 'n' threads. Waits until those threads have finished. Each thread
-- runs the supplied function given its thread ID in the range [0..n).
--
forkThreads :: Int -> (Int -> IO ()) -> IO ()
forkThreads n action = do
  -- Fork the threads and create a list of the MVars which per thread tell
  -- whether the action has finished.
  finishVars <- mapM work [0 .. n - 1]
  -- Once all the worker threads have been launched, now wait for them all to
  -- finish by blocking on their signal MVars.
  mapM_ takeMVar finishVars
  where
    -- Create a new empty MVar that is shared between the main (spawning) thread
    -- and the worker (child) thread. The main thread returns immediately after
    -- spawning the worker thread. Once the child thread has finished executing
    -- the given action, it fills in the MVar to signal to the calling thread
    -- that it has completed.
    --
    work :: Int -> IO (MVar ())
    work index = do
      done <- newEmptyMVar
      _    <- forkOn index (action index >> putMVar done ())  -- pin the worker to a given CPU core
      return done


printVerbose :: Bool -> String -> Graph -> Distance -> Buckets -> TentativeDistances -> IO ()
printVerbose verbose title graph delta buckets distances = when verbose $ do
  putStrLn $ "# " ++ title
  printCurrentState graph distances
  printBuckets graph delta buckets distances
  putStrLn "Press enter to continue"
  _ <- getLine
  return ()

-- Print the current state of the algorithm (tentative distance to all nodes)
--
printCurrentState
    :: Graph
    -> TentativeDistances
    -> IO ()
printCurrentState graph distances = do
  printf "  Node  |  Label  |  Distance\n"
  printf "--------+---------+------------\n"
  forM_ (G.labNodes graph) $ \(v, l) -> do
    x <- M.read distances v
    if isInfinite x
       then printf "  %4d  |  %5v  |  -\n" v l
       else printf "  %4d  |  %5v  |  %f\n" v l x
  --
  printf "\n"

printBuckets
    :: Graph
    -> Distance
    -> Buckets
    -> TentativeDistances
    -> IO ()
printBuckets graph delta Buckets{..} distances = do
  first <- readIORef firstBucket
  mapM_
    (\idx -> do
      let idx' = first + idx
      printf "Bucket %d: [%f, %f)\n" idx' (fromIntegral idx' * delta) ((fromIntegral idx'+1) * delta)
      b <- V.read bucketArray (idx' `rem` V.length bucketArray)
      printBucket graph b distances
    )
    [ 0 .. V.length bucketArray - 1 ]

-- Print a given bucket
--
printBucket
    :: Graph
    -> IntSet
    -> TentativeDistances
    -> IO ()
printBucket graph bucket distances = do
  printf "  Node  |  Label  |  Distance\n"
  printf "--------+---------+-----------\n"
  forM_ (Set.toAscList bucket) $ \v -> do
    let ml = G.lab graph v
    x <- M.read distances v
    case ml of
      Nothing -> printf "  %4d  |   -   |  %f\n" v x
      Just l  -> printf "  %4d  |  %5v  |  %f\n" v l x
  --
  printf "\n"

