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

import Statix.Syntax.Constraint
import Statix.Syntax.Parser
import Statix.Syntax.Lexer
import Statix.Analysis.Types
import Statix.Analysis.Typer
import Statix.Analysis.Namer
import Statix.Analysis.Symboltable
import Statix.Analysis
import Statix.Solver

import Debug.Trace

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
  let mark = if o then "[✓]" else "[✗]"
  describe (mark ++ " " ++ c) $ do
    -- parsing
    let tokens = lexer c
    trace ("TOKENS: " ++ show tokens) (return ())
    let parsed = tokens >>= runParser specmod . parseConstraint
    it "parses" $ do
      isRight tokens `shouldBe` True
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
    run True  "{x} f(x) = f(x)"
    run True  "{x, y} f(x) = y"
    run True  "{x, y} f(x) = f(g(y))"

    describe "occurs check" $ do
      run False "{x} f(x) = x"
      run False "{x} f(x) = g(x)"
      run False "{x, y} f(x) = g(y)"
      run False "{x, y} f(x) = f(g(x))"
      run False "{x, y} f(x) = g(f(x))"

    describe "n-ary" $ do
      run False "{x, y} f(x) = f(x, y)"
      run True  "{x, y} f(x, y) = f(y, x)"
      run False "{x, y} f(x, y) = f(y, x), x = f(y)"
      run False "{x, y} f(x, y) = g(x, y)"
  
    describe "transitive" $ do
      run True "{x, y} f() = x, x = y, y = f()"
      run False "{x, y} f() = x, x = y, y = g()"
      run False "{x, y} f(y) = x, x = y"
      run False "{x, y, z} f(x) = z, x = y, y = z"
      run True  "{x, y, z} f(x) = z, x = y, f(y) = z"

  describe "stuckness detection" $ do
    run False "{x, z} query x `P as z"
    run False "{x, y} x -[ P ]-> y"
    run True  "{x, y} x -[ P ]-> y, new x, new y"

newspec :: Spec
newspec = describe "new" $ do
    run True  "{x} new x"
    run False "{x} new x, new x"
    run True  "{x, y} new x, new y"

queryspec :: Spec
queryspec = describe "query" $ do
  describe "only" $ do
    run False "{x, y, z} new x, query x `l as y, only(y , z)"
    run True  "{x, y, z} new x, query x `l* as y, only(y , z)"
    run False "{x, y, z} new x, query x `l+ as y, only(y , z)"
    run False "{x, y, z} new x, query x `l`p as y, only(y , z)"
    run True  "{x,y,z,zt} new x, new y, x -[ l ]-> y, query x `l+ as z, only(z, zt)"
    run False "{x,y,yy,z,zt} new x, new y, new yy, x -[ l ]-> y, y -[ l ]-> yy, query x `l+ as z, only(z, zt)"
    run True  "{x,y,z,zt} new x, new y, x -[ l ]-> y, y -[ l ]-> x, query x `l+ as z, only(z, zt)"
    run False "{x,y,z,zt} new x, new y, x -[ l ]-> y, query x `l* as z, only(z, zt)"
    run True  "{x,y,z,zt} new x, new y, query x `l+ as z, x -[ l ]-> y, only(z, zt)"
    run False "{x,y,z,zt} new x, new y, query x `l* as z, x -[ l ]-> y, only(z, zt)"

  describe "every" $ do
    run True  "{x, y, z} new x, query x `l+ as y, every y (x -> false)"
    run True  "{x,y,yy,z,zt} new x, new y, new yy, x -[ l ]-> y, y -[ l ]-> yy, query x `l+ as z, every z (x -> true)"
    run False "{x,y,yy,z,zt} new x, new y, new yy, x -[ l ]-> y, y -[ l ]-> yy, query x `l+ as z, every z (x -> false)"    

  describe "min" $ do
    run False $ unlines
      [ "{x,y,z,d,ans} new x, new y, new z, new d"
      , ", x -[ a ]-> y, y -[ a ]-> z, x -[ b ]-> d, y -[ b ]-> d"
      , ", query x `a*`b as ans, {p} only(ans, p)"
      ]
      
    run True $ unlines
      [ "{x,y,z,d,ans} new x, new y, new z, new d"
      , ", x -[ a ]-> y, y -[ a ]-> z, x -[ b ]-> d, y -[ b ]-> d"
      , ", query x `a*`b as ans, {ps, p} min ans lexico(b < a) ps, only(ps, p)"
      ]
      
    run True $ unlines
      [ "{x,y,z,d,ans} new x, new y, new z, new d"
      , ", x -[ a ]-> y, y -[ a ]-> z, x -[ b ]-> d, y -[ b ]-> d"
      , ", query x `a*`b as ans, {ps, p} min ans lexico(a < b) ps, only(ps, p)"
      ]
      

  describe "filter" $ do
    run False $ unlines
      [ "{x,y,z} new x, new y, new z, x -[ A ]-> y, x -[ A ]-> z"
      , ", y -> f(), z -> g()"
      , ", {ans, p} query x `A as ans, only(ans, p)"
      ]

    run True $ unlines
      [ "{x,y,z} new x, new y, new z, x -[ A ]-> y, x -[ A ]-> z"
      , ", y -> f(), z -> g()"
      , ", {ans, ps, p} query x `A as ans, filter ans (d where d = f()) ps, only(ps, p)"
      ]
