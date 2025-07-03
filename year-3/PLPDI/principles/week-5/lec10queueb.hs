-- Queues, version B

module Queue(Queue,empty,enqueue,dequeue,peek) where

data Queue a = Q [a] [a]
-- A Queue implemented as a pair of lists:
--- First list is elements in order ready to go out.
--- Second list is elements in order most recent to come in.
-- Functions should try to keep the first list non-empty.

empty :: Queue a
empty = Q [] []

enqueue :: a -> Queue a -> Queue a
enqueue x (Q [] ys) = Q (reverse $ x:ys) []
enqueue x (Q xs ys) = Q xs (x:ys)

dequeue :: Queue a -> Queue a
dequeue (Q [] []) = Q [] []
-- dequeue (Q [] ys) = Q (reverse $ tail ys) [] -- hopefully never
dequeue (Q [x] ys) = Q (reverse ys) []
dequeue (Q (_:x:xs) ys) = Q (x:xs) ys

peek :: Queue a -> Maybe a
peek (Q [] []) = Nothing
-- peek (Q [] ys) = Just $ head ys -- hopefully never
peek (Q (x:_) _) = Just x
