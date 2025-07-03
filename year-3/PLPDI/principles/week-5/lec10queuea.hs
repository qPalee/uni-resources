-- Queues, version A

module Queue(Queue,empty,enqueue,dequeue,peek) where

data Queue a = Q [a]
-- A Queue implemented as a list:
--- The first element of the list is the next element to go out.

empty :: Queue a
empty = Q []

enqueue :: a -> Queue a -> Queue a
enqueue x (Q xs) = Q (xs ++ [x])

dequeue :: Queue a -> Queue a
dequeue (Q []) = Q []
dequeue (Q (_:xs)) = Q xs

peek :: Queue a -> Maybe a
peek (Q []) = Nothing
peek (Q (x:_)) = Just x
