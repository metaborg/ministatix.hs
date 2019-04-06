import Test.Hspec
import Text.Printf

import Data.Text
import Data.Default
import Data.Either
import Data.HashMap.Strict as HM

import Statix.Syntax.Constraint
import Statix.Syntax.Parser
import Statix.Analysis.Types
import Statix.Analysis
import Statix.Solver

main :: IO ()
main = hspec $ do
  corespec
  newspec
  queryspec

run :: Bool → String → Spec
run o c = do
  let mark = if o then "[✓]" else "[×]"
  describe (mark ++ " " ++ c) $ do
    -- parsing
    let result = runParser (pack "spec") (parseConstraint (lexer c))
    it "parses" $ do
      isRight result `shouldBe` True
    let parsed = fromRight undefined result

    -- static analysis
    let tcresult = runTC HM.empty $ analyze def parsed
    it "type checks" $ do
      isRight tcresult `shouldBe` True
    let typed = fst $ fromRight undefined tcresult

    -- dynamic semantics
    it "evaluates" $ do
      check HM.empty  typed `shouldBe` o

corespec :: Spec
corespec =
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

newspec :: Spec
newspec = describe "new" $ do
    run True  "{x} new x"
    run False "{x} new x, new x"
    run True  "{x, y} new x, new y"

queryspec :: Spec
queryspec = describe "query" $ do
    run False "{x, y, z} new x, query x `l as y, one(y , z)"
    run True  "{x, y, z} new x, query x `l* as y, one(y , z)"
    run False "{x, y, z} new x, query x `l+ as y, one(y , z)"
    run False "{x, y, z} new x, query x `l`p as y, one(y , z)"
    run True  "{x,y,z,zt} new x, new y, x -[ l ]-> y, query x `l+ as z, one(z, zt)"
    run False "{x,y,yy,z,zt} new x, new y, new yy, x -[ l ]-> y, y -[ l ]-> yy, query x `l+ as z, one(z, zt)"
    run True  "{x,y,z,zt} new x, new y, x -[ l ]-> y, y -[ l ]-> x, query x `l+ as z, one(z, zt)"
    run False "{x,y,z,zt} new x, new y, x -[ l ]-> y, query x `l* as z, one(z, zt)"
    run True  "{x,y,z,zt} new x, new y, query x `l+ as z, x -[ l ]-> y, one(z, zt)"
    run False "{x,y,z,zt} new x, new y, query x `l* as z, x -[ l ]-> y, one(z, zt)"
