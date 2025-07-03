import qualified Data.Set as Set



-- Arithmetic expressions

data Arith =
  T -- value
  | F -- value
  | Ite Arith Arith Arith
  | Zero -- value
  | Succ Arith -- Succ (value) is a value
  | Pred Arith
  | Iszero Arith
  deriving Show

size :: Arith -> Integer
size T = 1
size F = 1
size (Ite a b c) = 1 + size a + size b + size c
size Zero = 1
size (Succ a) = 1 + size a
size (Pred a) = 1 + size a
size (Iszero a) = 1 + size a

-- Language is not higher-order, so don't really have a
-- difference between CBV and CBN. (Maybe you could think
-- of different interpretations for ite).
eval :: Arith -> Maybe Arith
eval T = Just T
eval F = Just F
eval Zero = Just Zero
eval (Ite a b c) =
  do a' <- eval a
     case a' of
       T -> eval b
       F -> eval c
       _ -> Nothing
eval (Succ a) =
  do a' <- eval a
     return $ Succ a'
eval (Pred a) =
  do a' <- eval a
     case a' of
       Zero -> return Zero
       Succ x -> return x
       _ -> Nothing
eval (Iszero a) =
  do a' <- eval a
     case a' of
       Zero -> return T
       Succ x -> return F
       _ -> Nothing


step :: Arith -> Maybe Arith
step T = Nothing
step F = Nothing
step (Ite T b _) = Just b
step (Ite F _ c) = Just c
step (Ite a b c) = do a' <- step a; return $ Ite a' b c
step Zero = Nothing
step (Succ a) = do a' <- step a; return $ Succ a'
step (Pred Zero) = Just Zero
step (Pred (Succ a)) = Just a
step (Pred x) = do x' <- step x; return $ Pred x'
step (Iszero Zero) = Just T
step (Iszero (Succ _)) = Just F
step (Iszero a) = do a' <- step a; return $ Iszero a'


-- Try at most n steps
multistep :: Int -> Arith -> [Arith]
multistep n a = do x <- take n $ iterate (>>= step) (Just a)
                   case x of
                     Just y -> return y
                     Nothing -> []

printMultistep :: Int -> Arith -> IO ()
printMultistep n a = mapM_ print $ multistep n a







-- Set up a type synonym for variables.
-- Any infinite type would do.
type Var = String

data LTerm = Var Var
         | Lam Var LTerm
         | App LTerm LTerm

instance Show LTerm where
  show (Var x) = x
  show (Lam x t) = "(λ" ++ x ++ "." ++ (show t) ++ ")"
  show (App s t) = "(" ++ show s ++ " " ++ show t ++ ")"

-- λx.x
t1 = Lam "x" (Var "x")
-- λx.λy.x
t2 = Lam "x" (Lam "y" (Var "x"))
-- λx.λy.y
t3 = Lam "x" (Lam "y" (Var "y"))
-- (λx.x)(λx.x)
t4 = App (Lam "x" (Var "x")) (Lam "x" (Var "x"))

-- λx.λy.xy
-- (λx.(λy.(xy)))
t5 = (Lam "x" (Lam "y" (App (Var "x") (Var "y"))))
-- t5 = Lam "x" $ Lam "y" $ App (Var "x") (Var "y")

-- λx.xλx.xx
-- (λx.(x(λx.(xx))))
t6 = Lam "x" $ App (Var "x") (Lam "x" $ App (Var "x") (Var "x"))

-- (λx.((xx)(λx.x)))
t7 = Lam "x" $ App (App (Var "x") (Var "x")) (Lam "x" (Var "x"))

ω = Lam "x" $ Var "x" `App` Var "x" -- AKA Δ
cΩ = ω `App` ω -- AKA ΔΔ

-- TODO
-- Make the following parse as expected:
-- Var "x" `App` Lam "y" $ Var "y"

freeVars :: LTerm -> Set.Set Var
freeVars (Var c) = Set.singleton(c)
freeVars (Lam c t) = Set.delete c (freeVars t)
freeVars (App s t) = Set.union (freeVars s) (freeVars t)

freshFor :: Set.Set Var -> Var
freshFor xs = let freshForAux x xs
                    | x `elem` xs = freshForAux ('\'':x) xs
                    | otherwise   = x
              in freshForAux "a" xs

-- Check for alpha-equivalence
(==@) :: LTerm -> LTerm -> Bool
Var x ==@ Var y = x == y
Lam x u ==@ Lam y v
  | x == y    = u ==@ v
  | otherwise = let z = freshFor $ freeVars u `Set.union` freeVars v
                    u' = varSubst x z u
                    v' = varSubst y z v
                in u' ==@ v'
App u1 u2 ==@ App v1 v2 = u1 ==@ u2 && v1 ==@ v2
_ ==@ _ = False

-- If a variable is in a set of variables, suggest what to rename it to.
freshen :: Var -> Set.Set Var -> Var
freshen x ys | x `elem` ys = freshen (x ++ "'") ys
             | otherwise   = x

-- Perform the renaming of the first variable to the second
-- to get an alpha-equivalent term
varSubst :: Var -> Var -> LTerm -> LTerm
varSubst x y (Var z)
  | x == z    = Var y
  | otherwise = Var z
varSubst x y (Lam z t)
  | x == z    = Lam z t
  | otherwise = Lam z $ varSubst x y t
varSubst x y (App u v)
  = let u' = varSubst x y u
        v' = varSubst x y v
    in App u' v'

-- Performs an alpha-renaming when necessary
captureAvoidingSubst :: LTerm -> Var -> LTerm -> LTerm
captureAvoidingSubst (Var x) y t
  | x == y    = t
  | otherwise = Var x
captureAvoidingSubst (Lam x u) y t
  | x == y
  = Lam x u
  | x `elem` freeVars t
  = let z = freshen x $ freeVars t `Set.union` freeVars u
        u' = varSubst x z u
    in Lam z $ captureAvoidingSubst u' y t
  | otherwise = Lam x $ captureAvoidingSubst u y t
captureAvoidingSubst (App u v) y t
  = let u' = captureAvoidingSubst u y t
        v' = captureAvoidingSubst v y t
    in App u' v'
