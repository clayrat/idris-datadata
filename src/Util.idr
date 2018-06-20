module Util

%default total
%access public export

infixr 9 .%

-- compare to prelude's:
--   (.) : (b -> c) -> (a -> b) -> a -> c 
--   (.) f g = \x => f (g x)              
-- in contrast, this definition allows us to actually prove things, because lambdas in types break everything spectacularly
(.%) : (b -> c) -> (a -> b) -> a -> c 
(.%) f g x = f (g x)