import qualified Data.Set as Set


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

ω = Lam "x" $ Var "x" `App` Var "x"
cΩ = ω `App` ω

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

-- Try to do at least one beta reduction
oneBetaWithAlphaShift :: LTerm -> LTerm
oneBetaWithAlphaShift (Var x) = Var x
oneBetaWithAlphaShift (Lam x u) = Lam x $ oneBetaWithAlphaShift u
oneBetaWithAlphaShift (App (Lam x u) v) = captureAvoidingSubst u x v
oneBetaWithAlphaShift (App u v)
  = let u' = oneBetaWithAlphaShift u
        v' = oneBetaWithAlphaShift v
    in App u' v'

-- CBV big step
cbv :: LTerm -> LTerm
cbv (Var v) = Var v
cbv (Lam x u) = Lam x u
cbv (App s t)
  = case cbv s of
      Lam x u -> let b = cbv t in cbv (captureAvoidingSubst u x b)
      a -> App a t

-- CBN big step
cbn :: LTerm -> LTerm
cbn (Var v) = Var v
cbn (Lam x u) = Lam x u
cbn (App s t)
  = case cbn s of
      Lam x u -> cbn (captureAvoidingSubst u x t)
      a -> App a t

-- CBV small step
cbvStep :: LTerm -> Maybe LTerm
cbvStep (Var _) = Nothing
cbvStep (Lam _ _) = Nothing
cbvStep (App (Lam x u) t@(Lam _ _)) = Just $ captureAvoidingSubst u x t
cbvStep (App s@(Lam _ _) t)
  = do
  t' <- cbvStep t
  return $ App s t'
cbvStep (App s t)
  = do
  s' <- cbvStep s
  return $ App s' t

-- CBN small step
cbnStep :: LTerm -> Maybe LTerm
cbnStep (Var _) = Nothing
cbnStep (Lam _ _) = Nothing
cbnStep (App (Lam x u) t) = Just $ captureAvoidingSubst u x t
cbnStep (App s t)
  = do
  s' <- cbnStep s
  return $ App s' t

-- Normal order stuff is not tested
normalOrder :: LTerm -> LTerm
normalOrder (Var x) = Var x
normalOrder (Lam x u) = Lam x $ normalOrder u
normalOrder (App s t)
  = case cbn s of
      Lam x u -> normalOrder $ captureAvoidingSubst u x t
      m       -> App m $ normalOrder t

normalOrderStep :: LTerm -> Maybe LTerm
normalOrderStep (Var _) = Nothing
normalOrderStep (Lam x u)
  = do
  u' <- normalOrderStep u
  return $ Lam x u'
normalOrderStep (App s@(Lam x u) t)
  | isNormal s = Just $ captureAvoidingSubst u x t
  | otherwise = normalOrderStep s >>= \s' -> return $ App s' t
normalOrderStep (App s t)
  | isNormal s = normalOrderStep t >>= \t' -> return $ App s t'
  | otherwise = normalOrderStep s >>= \s' -> return $ App s' t


-- Test for beta-normal forms
isNormal :: LTerm -> Bool
isNormal (Var _) = True
isNormal (Lam _ t) = isNormal t
isNormal (App (Lam _ _) _) = False
isNormal (App s t) = isNormal s && isNormal t

redexes :: LTerm -> [LTerm]
redexes (Var _) = []
redexes (Lam _ t) = redexes t
redexes t@(App (Lam _ u) v) = t : redexes u ++ redexes v
redexes (App u v) = redexes u ++ redexes v


-- Sample lambda terms to help with testing
lT = Lam "x" $ Lam "y" $ Var "x"
lF = Lam "x" $ Lam "y" $ Var "y"
lAnd = Lam "a" $ Lam "b" $ App (App (Var "a") (Var "b")) lF
-- lAnd = Lam "a" $ Lam "b" $ Var "a" `App` Var "b" `App` lF
lOr = Lam "a" $ Lam "b" $ App (App (Var "a") lT) (Var "b")
lNot = Lam "a" $ App (App (Var "a") lF) lT



-- Use
-- mapM_ print $
-- in front to get printing per line.

-- Try at most n steps
multistep :: Int -> (LTerm -> Maybe LTerm) -> LTerm -> [LTerm]
multistep n step a = do x <- take n $ iterate (>>= step) (Just a)
                        case x of
                          Just y -> return y
                          Nothing -> []

steptest :: (LTerm -> Maybe LTerm) -> LTerm -> IO ()
steptest step a = mapM_ print $ multistep 100 step a



-- NB When looking at CBV and CBN semantics of closed terms,
-- you will never need to alpha-rename to avoid capture.
-- This is because you never reduce 'under a lambda', so in
-- particular beta-reductions never happen under the scope of
-- a lambda, so we only every substitute in closed terms.
-- To test the alpha-conversion, we need to try examples with
-- open terms.

exl4s8d = (Lam "x" $ Lam "y" $ Var "y" `App` Var "x") `App` (Var "y" `App` Var "y")

-- steptest cbvStep exl4s8d
-- steptest cbnStep exl4s8d
