-- Counters, various versions

-- module Counter where

-- type Counter = Integer

-- new :: Counter
-- new = 0

-- get :: Counter -> Integer
-- get c = c

-- inc :: Counter -> Counter
-- inc c = c + 1


-- module Counter where

-- data Counter = C Integer

-- new :: Counter
-- new = C 0

-- get :: Counter -> Integer
-- get (C c) = c

-- inc :: Counter -> Counter
-- inc (C c) = C (c + 1)



module Counter(Counter,new,get,inc) where

data Counter = C Integer

new :: Counter
new = C 0
  
get :: Counter -> Integer
get (C c) = c

inc :: Counter -> Counter
inc (C c) = C (c + 1)

