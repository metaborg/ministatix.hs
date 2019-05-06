import Test.Hspec
import Text.Printf

import Data.Text hiding (unlines)
import Data.Default
import Data.Either
import Data.HashMap.Strict as HM

import Control.Lens
import Control.Monad.ST
import Control.Monad.Identity
import Control.Monad.Except
import Control.Monad.State

import Statix.Syntax
import Statix.Syntax.Parser
import Statix.Analysis.Types
import Statix.Analysis.Typer
import Statix.Analysis.Namer
import Statix.Analysis.Symboltable
import Statix.Analysis
import Statix.Solver

main :: IO ()
main = hspec $ do
  corespec
  newspec
  queryspec

specmod :: Text
specmod = pack "spec"


runMod :: Bool → RawModule → Text → Spec
runMod o rawmod main = do
  let mod      = runIdentity $ runExceptT $
        evalStateT (analyze specmod HM.empty rawmod) (0 :: Integer)

  it "analyzes" $ do
    isRight mod `shouldBe` True

  -- dynamic semantics
  it "evaluates" $ do
    check HM.empty (body $ (HM.! main) $ fromRight undefined mod) `shouldBe` o

run :: Bool → String → Spec
run o c = do
  let mark = if o then "[✓]" else "[×]"
  describe (mark ++ " " ++ c) $ do
    -- parsing
    let parsed = parseConstraint specmod c
    it "parses" $ do
      isRight parsed `shouldBe` True

    -- static analysis
    let rawbody  = fromRight undefined parsed
    let testpred = pack "test"
    let qn       = (specmod, testpred)
    let rawmod   = Mod [] [Pred qn [] rawbody]

    runMod o rawmod testpred

corespec :: Spec
corespec = do
  describe "equality" $ do
    run True  "{x} x = x"
    run True  "{x, y} x = y"
    run True  "{x} F(x) = F(x)"
    run True  "{x, y} F(x) = y"
    run True  "{x, y} F(x) = F(G(y))"

    describe "occurs check" $ do
      run False "{x} F(x) = x"
      run False "{x} F(x) = G(x)"
      run False "{x, y} F(x) = G(y)"
      run False "{x, y} F(x) = F(G(x))"
      run False "{x, y} F(x) = G(F(x))"

    describe "n-ary" $ do
      run False "{x, y} F(x) = F(x, y)"
      run True  "{x, y} F(x, y) = F(y, x)"
      run False "{x, y} F(x, y) = F(y, x), x = F(y)"
      run False "{x, y} F(x, y) = G(x, y)"
  
    describe "transitive" $ do
      run True "{x, y} F() = x, x = y, y = F()"
      run False "{x, y} F() = x, x = y, y = G()"
      run False "{x, y} F(y) = x, x = y"
      run False "{x, y, z} F(x) = z, x = y, y = z"
      run True  "{x, y, z} F(x) = z, x = y, F(y) = z"

  describe "stuckness detection" $ do
    run False "{x, z} query x `P as z"
    run False "{x, y} x -[ `P ]-> y"
    run True  "{x, y} x -[ `P ]-> y, new x, new y"

newspec :: Spec
newspec = describe "new" $ do
    run True  "{x} new x"
    run False "{x} new x, new x"
    run True  "{x, y} new x, new y"

queryspec :: Spec
queryspec = describe "query" $ do
  describe "only" $ do
    run False "{x, y, z} new x, query x `L as y, only(y , z)"
    run True  "{x, y, z} new x, query x `L* as y, only(y , z)"
    run False "{x, y, z} new x, query x `L+ as y, only(y , z)"
    run False "{x, y, z} new x, query x `L`P as y, only(y , z)"
    run True  "{x,y,z,zt} new x, new y, x -[ `L ]-> y, query x `L+ as z, only(z, zt)"
    run False "{x,y,yy,z,zt} new x, new y, new yy, x -[ `L ]-> y, y -[ `L ]-> yy, query x `L+ as z, only(z, zt)"
    run False "{x,y,z,zt} new x, new y, x -[ `L ]-> y, y -[ `L ]-> x, query x `L+ as z, only(z, zt)"
    run False "{x,y,z,zt} new x, new y, x -[ `L ]-> y, query x `L* as z, only(z, zt)"
    run True  "{x,y,z,zt} new x, new y, query x `L+ as z, x -[ `L ]-> y, only(z, zt)"
    run False "{x,y,z,zt} new x, new y, query x `L* as z, x -[ `L ]-> y, only(z, zt)"
    run False "{x, y} new x, new y, x -[ `L ]-> y, x -[ `R ]-> y, {ps, p} query x `L|`R as ps, only(ps , p)"
    run True  "{x, y} new x, new y, x -[ `L ]-> y, {ps, p} query x `L|`R as ps, only(ps , p)"
    run True  "{x, y} new x, new y, x -[ `R ]-> y, {ps, p} query x `L|`R as ps, only(ps , p)"
    run True  "{x, y} new x, new y, x -[ `R ]-> y, {ps, p} query x ~(`L*) as ps, only(ps , p)"
    run False "{x, y} new x, new y, x -[ `R ]-> y, {ps, p} query x ~(`R*) as ps, only(ps , p)"

  describe "every" $ do
    run True  "{x, y, z} new x, query x `L+ as y, every y (x -> false)"
    run True  "{x,y,yy,z,zt} new x, new y, new yy, x -[ `L ]-> y, y -[ `L ]-> yy, query x `L+ as z, every z (x -> true)"
    run False "{x,y,yy,z,zt} new x, new y, new yy, x -[ `L ]-> y, y -[ `L ]-> yy, query x `L+ as z, every z (x -> false)"    

  describe "min" $ do
    run False $ unlines
      [ "{x,y,z,d,ans} new x, new y, new z, new d"
      , ", x -[ `A ]-> y, y -[ `A ]-> z, x -[ `B ]-> d, y -[ `B ]-> d"
      , ", query x `A*`B as ans, {p} only(ans, p)"
      ]
      
    run True $ unlines
      [ "{x,y,z,d,ans} new x, new y, new z, new d"
      , ", x -[ `A ]-> y, y -[ `A ]-> z, x -[ `B ]-> d, y -[ `B ]-> d"
      , ", query x `A*`B as ans, {ps, p} min ans lexico(`B < `A) ps, only(ps, p)"
      ]
      
    run True $ unlines
      [ "{x,y,z,d,ans} new x, new y, new z, new d"
      , ", x -[ `A ]-> y, y -[ `A ]-> z, x -[ `B ]-> d, y -[ `B ]-> d"
      , ", query x `A*`B as ans, {ps, p} min ans lexico(`A < `B) ps, only(ps, p)"
      ]
      

  describe "filter" $ do
    run False $ unlines
      [ "{x} new x, x -> F()" ]

    run False $ unlines
      [ "{x} new x -> F(), x -> G()" ]

    run False $ unlines
      [ "{x,y,z} new x, new y -> F(), new z -> G(), x -[ `A ]-> y, x -[ `A ]-> z"
      , ", {ans, p} query x `A as ans, only(ans, p)"
      ]

    run True $ unlines
      [ "{x,y,z} new x, new y -> F(), new z -> G(), x -[ `A ]-> y, x -[ `A ]-> z"
      , ", {ans, ps, p} query x `A as ans, filter ans (d where d = F()) ps, only(ps, p)"
      ]

  describe "lists" $ do
    run True "(F():G():[]) match { (F():G():[]) -> true }"
