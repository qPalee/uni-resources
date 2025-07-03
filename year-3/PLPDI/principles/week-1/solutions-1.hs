{- 1. Areas of shapes -}

data Shape = Circle Double
           | Rectangle Double Double

-- Write a function area:
area :: Shape -> Double
area (Circle r) = pi * r * r
area (Rectangle h w) = h * w

-- Alternatively
area' = (\x -> case x of { Circle r -> pi * r * r; Rectangle h w -> h * w })

{- 2. Inductive datatypes -}

data MixList = MNil
             | IntCons Int MixList
             | BoolCons Bool MixList
             deriving Show

{-
A value of the form
MNil
represents an empty list

A value of the form
IntCons n xs
represents a list whose first element is an integer n and whose tail is xs

A value of the form
BoolCons b xs
represents a list whose first element is a boolean b and whose tail is xs

The IntCons's and BoolCons's can be interleaved arbitrarilyl, so we can mix integer and boolean values in the list however we like.
-}

squareDrop :: MixList -> MixList
squareDrop MNil = MNil
squareDrop (IntCons n ms) = IntCons (n * n) (squareDrop ms)
squareDrop (BoolCons _ ms) = squareDrop ms

-- Write a function dropNot:
dropNot :: MixList -> MixList
dropNot MNil = MNil
dropNot (IntCons _ ms) = dropNot ms
dropNot (BoolCons b ms) = BoolCons (not b) ms

-- Extension part. Write mapDrop:
mapDrop :: (Int -> Int) -> MixList -> MixList
mapDrop _ MNil = MNil
mapDrop f (IntCons n ms) = IntCons (f n) (mapDrop f ms)
mapDrop f (BoolCons _ ms) = mapDrop f ms

-- Check.
-- The next line allows us write q2textlist without brackets
infixr 5 `IntCons`, `BoolCons`

q2testlist = 1 `IntCons` True `BoolCons` 3 `IntCons` False `BoolCons` MNil
q2test1 = squareDrop q2testlist
q2test2 = mapDrop (\n -> n * n) q2testlist


{- 3. Negate a list -}

negateAll :: [Integer] -> [Integer]
negateAll [] = []
negateAll (x:xs) = (-x):(negateAll xs)

-- N.B. A standard way to write this in Haskell is using map:
negateAll' = map negate


{- 4. Checking for an element -}

myElem :: Integer -> [Integer] -> Bool
myElem _ [] = False
myElem n (x:xs) = if n == x then True else myElem n xs


{- 5. Safely searching for an element -}

-- Approach 1a: use a helper function with an extra argument
-- The extra Integer argument is used to count how many recursive calls have been made
findaux :: Integer -> Integer -> [Integer] -> Maybe Integer
findaux _ _ [] = Nothing
findaux m n (x:xs) = if n == x then Just m else findaux (m+1) n xs
-- Then find is given by partially applying findaux
find :: Integer -> [Integer] -> Maybe Integer
find = findaux 0

-- Approach 1b: use a helper function but keep it local
find' :: Integer -> [Integer] -> Maybe Integer
find' n xs = let findaux' _ _ [] = Nothing
                 findaux' m n (x:xs) = if n == x then Just m else findaux' (m+1) n xs
             in findaux' 0 n xs

-- Approach 2: without using an extra argument
-- This is probably a bit worse, since it not 'tail-recursive'
find'' :: Integer -> [Integer] -> Maybe Integer
find'' _ [] = Nothing
find'' x (y:ys) = if x == y then Just 0
                  else case find'' x ys of
                         Nothing -> Nothing
                         Just n -> Just (n+1)


{- 6. Check a list for positives -}

allPositive :: [Integer] -> Bool
allPositive [] = True
allPositive (x:xs) = (x > 0) && (allPositive xs)

-- Bonus: point-free using map, fold, and function composition (.)
allPositive' = (foldr (&&) True) . (map (0<))


{- 7. Find all positives in a list -}

positives :: [Integer] -> [Integer]
positives [] = []
positives (x:xs) = if x > 0 then x:(positives xs) else (positives xs)

-- Bonus: point-free using filter
positives' = filter (0<)


{- 8. Inline pattern-matching -}

-- g reverses a list.
-- Its helper function f unpacks its first list argument onto its
-- second list argument, in the process reversing the order of the
-- elements in the first argument.

f [] ys = ys
f (x:xs) ys = f xs (x:ys)

g m = f m []


{- 9. Check for sortedness -}

sorted :: [Integer] -> Bool
sorted [] = True
sorted [a] = True
sorted (a:b:l) = (a <= b) && sorted (b:l)


{- 10. Enumerations -}

-- Approach 1
enumerate = let enumaux n = n : enumaux (n+1)
            in enumaux 0

-- Bonus approach 2: as a fixed point

fix f = f (fix f)

enumerate' = fix (\l -> 0 : map (+1) l)


progress f n = f (progress f) n

enumerate'' = fix (\f n -> n : f (n+1)) 0
