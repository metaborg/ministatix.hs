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

run :: String → Bool → Spec
run c o = do
  let mark = if o then "[✓]" else "[×]"
  describe (mark ++ " " ++ c) $ do
    -- parsing
    let result = runParser (pack "spec") (parseConstraint (lexer c))
    it "parses" $ do
      isRight result `shouldBe` True
    let parsed = fromRight undefined result
    -- static analysis
    let (tcresult , _) = runTC HM.empty $ analyze def parsed
    it "type checks" $ do
      isRight tcresult `shouldBe` True
    let typed = fromRight undefined tcresult
    -- dynamic semantics
    it "evaluates" $ do
      check HM.empty  typed `shouldBe` o

corespec :: Spec
corespec =
  describe "core" $ do
    run "{x} x = x" True
    run "{x, y} x = y" True
    run "{x} f(x) = x" False
    run "{x, y} f(x) = y" True

newspec :: Spec
newspec = describe "new" $ do
    run "{x} new x" True
    run "{x} new x, new x" False
    run "{x, y} new x, new y" True

queryspec :: Spec
queryspec = describe "query" $ do
    run "{x, y, z} new x, query x `l as y, one(y , z)" False
    run "{x, y, z} new x, query x `l* as y, one(y , z)" True
    run "{x, y, z} new x, query x `l+ as y, one(y , z)" False
    run "{x, y, z} new x, query x `l`p as y, one(y , z)" False
    run "{x,y,z,zt} new x, new y, x -[ l ]-> y, query x `l+ as z, one(z, zt)" True
    run "{x,y,z,zt} new x, new y, x -[ l ]-> y, query x `l* as z, one(z, zt)" False
