import Test.Hspec
import Text.Printf

import Statix.Solver

main :: IO ()
main = hspec $ do
  corespec
  newspec
  queryspec

corespec :: Spec
corespec =
  describe "core" $ do
    it "[✓] ∃ x. x = x" $ do
      check "{x} x = x" `shouldBe` True

    it "[✓] ∃ x y. x = y" $ do
      check "{x, y} x = y" `shouldBe` True

    it "[×] ∃ x. f(x) = x" $ do
      check "{x} f(x) = x" `shouldBe` False

    it "[×] ∃ x y. f(x) = y" $ do
      check "{x, y} f(x) = y" `shouldBe` True

newspec :: Spec
newspec = describe "new" $ do
    it "[✓] ∃ x . new x" $ do
      check "{x} new x" `shouldBe` True

    it "[×] ∃ x . new x, new x" $ do
      check "{x} new x, new x" `shouldBe` False

    it "[✓] ∃ x y . new x, new y" $ do
      check "{x, y} new x, new y" `shouldBe` True

queryspec :: Spec
queryspec = describe "query" $ do
    it "[×] new x, query x `l as y, one(y , z)" $ do
      check "{x, y, z} new x, query x `l as y, one(y , z)" `shouldBe` False

    it "[✓] new x, query x `l* as y, one(y , z)" $ do
      check "{x, y, z} new x, query x `l* as y, one(y , z)" `shouldBe` True

    it "[×] new x, query x `l+ as y, one(y , z)" $ do
      check "{x, y, z} new x, query x `l+ as y, one(y , z)" `shouldBe` False

    it "[×] new x, query x `l`p as y, one(y , z)" $ do
      check "{x, y, z} new x, query x `l`p as y, one(y , z)" `shouldBe` False

    it "[✓] new x, new y, x -[ l ]-> y, query x `l+ as z, one(z, zt)" $ do
      check "{x,y,z,zt} new x, new y, x -[ l ]-> y, query x `l+ as z, one(z, zt)" `shouldBe` True

    it "[×] new x, new y, x -[ l ]-> y, query x `l* as z, one(z, zt)" $ do
      check "{x,y,z,zt} new x, new y, x -[ l ]-> y, query x `l* as z, one(z, zt)" `shouldBe` False
