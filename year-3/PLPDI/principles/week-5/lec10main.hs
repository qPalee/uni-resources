module Main where

-- import Counter

import Queue

-- break :: Counter -> Integer
-- break c = c

-- break :: Counter -> Integer
-- break (C c) = c

-- x = inc $ inc $ new

-- main = print (get x)

y = enqueue 1 $ enqueue 2 $ empty

main = print (peek y)
