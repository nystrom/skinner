-- Experiment with name matching using linear programming

import qualified Data.Map as Map
import Data.Tuple (swap)
import Data.Maybe (fromJust)
import Control.Monad
import Numeric.LinearProgramming

main :: IO ()
main = do

  let (##) a b = a ++ "#" ++ b
  infixl 6 ##
  let add = "Add"
  let add' = "Add'"
  let sub = "Sub"
  let sub' = "Sub'"
  let exp = "Exp"
  let exp' = "Exp'"
  let cast = "Cast"
  let cast' = "Cast'"
  let typ = "Type"
  let typ' = "Type'"
  let junk = "Junk"

  let top = 1e6

  let labels :: [ (String, Double) ]
      labels = [ (add##add', 0),
                 (add##sub', 100),
                 (add##cast', 100),
                 (sub##add', 100),
                 (sub##sub', 0),
                 (sub##cast', 100),
                 (cast##add', 100),
                 (cast##sub', 100),
                 (cast##cast', 0),
                 (junk##add', 100),
                 (junk##sub', 100),
                 (junk##cast', 100),
                 (exp##exp', 0),
                 (exp##typ', 100),
                 (typ##exp', 100),
                 (typ##typ', 0) ]

  -- TODO replace with reader
  let nodeMap = Map.fromList (map fst labels `zip` [1..])
  let revNodeMap = Map.fromList ([1..] `zip` map fst labels)

  let p s = 1 # (fromJust $ Map.lookup s nodeMap)
  let n s = (-1) # (fromJust $ Map.lookup s nodeMap)
  let problem = Maximize $ map ((top-) . snd) labels

  let (==>) s t = [ p s, n t ] :<=: 0
      infixl 4 ==>
  let oneOf ss = (map p ss) :<=: 1

  let constraints = Sparse [
          oneOf [add##add', sub##add', cast##add', junk##add' ],
          oneOf [add##sub', sub##sub', cast##sub', junk##sub' ],
          oneOf [add##cast', sub##cast', cast##cast', junk##cast' ],

          oneOf [add##add', add##sub', add##cast' ],
          oneOf [sub##add', sub##sub', sub##cast' ],
          oneOf [cast##add', cast##sub', cast##cast' ],
          oneOf [junk##add', junk##sub', junk##cast' ],

          oneOf [exp##exp', exp##typ' ],
          oneOf [typ##exp', typ##typ' ],

          add##add' ==> exp##exp',
          sub##add' ==> exp##exp',
          cast##add' ==> exp##exp',
          cast##add' ==> typ##exp',

          add##sub' ==> exp##exp',
          sub##sub' ==> exp##exp',
          cast##sub' ==> exp##exp',
          cast##sub' ==> typ##exp',

          add##cast' ==> exp##exp',
          add##cast' ==> exp##typ',
          sub##cast' ==> exp##exp',
          sub##cast' ==> exp##typ',
          cast##cast' ==> exp##exp',
          cast##cast' ==> typ##typ'
        ]

  let soln = simplex problem constraints []
  putStrLn $ show soln

  case soln of
    Optimal(cost, coeffs) ->
      forM_ (coeffs `zip` labels) $ \(alpha, (label, dist)) -> do
        let n = floor alpha
        if n == 0
          then return ()
          else putStrLn $ label ++ " " ++ show n
    _ -> return ()

  {-
   - forM_ soln $ \(v,w,(maxCap,currentFlow,resCap)) -> do
    let vlabel = fromJust $ Map.lookup v revNodeMap
    let wlabel = fromJust $ Map.lookup w revNodeMap
    when (currentFlow > 0 && v /= source && w /= sink) $
      putStrLn $ vlabel ++ " -> " ++ wlabel ++ " " ++ show currentFlow
  return ()
  -}

