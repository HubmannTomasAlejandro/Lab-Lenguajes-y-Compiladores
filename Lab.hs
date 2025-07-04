{-# LANGUAGE GADTs, TypeSynonymInstances, FlexibleInstances #-}
import Control.Applicative ( liftA, liftA2 )


type Var = String
type Σ   = Var -> Int

{- Dominios semánticos -}
type MInt  = Maybe Int  -- { n | (n = Just m, m ∈ Int)    ∨ (n = Nothing) }
type MBool = Maybe Bool -- { b | (b = Just b', b' ∈ Bool) ∨ (b = Nothing) }

{- Ω ≈ (Σ' + Z × Ω + Z → Ω)⊥ -}
data Ω = Normal Σ | Abort Σ | Out (Int, Ω) | In (Int -> Ω)
{- Notar:
   * Normal : Σ → Ω
   * Abort  : Σ → Ω
   * Out    : (Z, Ω) → Ω
   * In     : (Z → Ω) → Ω
-}

data Expr a where
  -- # Expresiones enteras
  Const :: Int         -> Expr MInt                          -- n
  Var   :: Var         -> Expr MInt                          -- v
  Plus  :: Expr MInt   -> Expr MInt  -> Expr MInt            -- e + e'
  Prod  :: Expr MInt   -> Expr MInt  -> Expr MInt            -- e * e'
  Div   :: Expr MInt   -> Expr MInt  -> Expr MInt            -- e / e'
  Op    :: Expr MInt   -> Expr MInt                          -- - e
  -- # Expresiones booleanas
  CBool :: Bool        -> Expr MBool                          -- b
  Not   :: Expr MBool  -> Expr MBool                          -- ¬ b
  And   :: Expr MBool  -> Expr MBool -> Expr MBool            -- b ∧ b'
  Or    :: Expr MBool  -> Expr MBool -> Expr MBool            -- b ∨ b'
  -- Comparacion
  Eq    :: Expr MInt   -> Expr MInt  -> Expr MBool            -- e = e'
  Lt    :: Expr MInt   -> Expr MInt  -> Expr MBool            -- e < e'
  Gt    :: Expr MInt   -> Expr MInt  -> Expr MBool            -- e > e'
  GtE   :: Expr MInt   -> Expr MInt  -> Expr MBool            -- e >= e'
  LtE   :: Expr MInt   -> Expr MInt  -> Expr MBool            -- e <= e'
  -- # Comandos LIS
  Skip   :: Expr Ω                                            -- skip
  Assign :: Var        -> Expr MInt  -> Expr Ω                -- v := e
  Seq    :: Expr Ω     -> Expr Ω     -> Expr Ω                -- c ; c'
  Cond   :: Expr MBool -> Expr Ω     -> Expr Ω -> Expr Ω      -- if b then c else c'
  Newvar :: Var        -> Expr MInt  -> Expr Ω -> Expr Ω      -- newvar v := e in e'
  While  :: Expr MBool -> Expr Ω     -> Expr Ω                -- while b do c
  -- # Comandos Fallas
  Fail   :: Expr Ω                                            -- fail
  Catch  :: Expr Ω     -> Expr Ω     -> Expr Ω                -- catch c with c'
  -- # Comandos IO
  SOut   :: Expr MInt  -> Expr Ω                              -- !e
  SIn    :: Var        -> Expr Ω                              -- ?v

{- Funciones auxiliares para la semantica -}
--         ∞
-- fix f = ⊔ fⁱ ⊥
--        i=0
fix :: (a -> a) -> a
fix f = f (fix f)

update :: Σ -> Var -> Int -> Σ
update σ v n v' = if v == v' then n else σ v'

rest :: Σ -> Var -> (Σ -> Σ)
rest σ v σ' v'= if v == v' then σ v else σ' v'

f_big :: Expr MBool -> Expr Ω ->(Σ -> Ω) -> (Σ -> Ω)
f_big b c = \f -> \σ -> (case (sem b σ) of
    Just False -> Normal σ
    Just True  -> (f *.) (sem c σ)
    _ -> Abort σ)

(-^-) :: (a -> b -> c) -> (Maybe a -> Maybe b -> Maybe c)
(-^-) = liftA2

(-^) :: (a -> b) -> (Maybe a -> Maybe b)
(-^) = liftA

(>>==) :: (Maybe a, Σ) -> (a -> Ω) -> Ω
(>>==) (Nothing, σ) _ = Abort σ
(>>==) (Just n, _)  f = f n

(*.) :: (Σ -> Ω) -> Ω -> Ω
(*.) f (Normal σ)  = f σ
(*.) _ (Abort σ)   = Abort σ
(*.) f (Out (n,ω)) = Out (n, f *. ω)
(*.) f (In g)      = In ((f *.) . g)

(†.) :: (Σ -> Σ) -> Ω -> Ω
(†.) f (Normal σ)  = Normal $ f σ
(†.) f (Abort σ)   = Abort $ f σ
(†.) f (Out (n,ω)) = Out (n, f †. ω)
(†.) f (In g)      = In ((f †.) . g)

(+.) :: (Σ -> Ω) -> Ω -> Ω
(+.) _ (Normal σ)  = Normal σ
(+.) f (Abort σ)   = f σ
(+.) f (Out (n,ω)) = Out (n, f +. ω)
(+.) f (In g)      = In ((f +.) . g)


{- Semántica de evaluación -}
class DomSem dom where
  sem :: Expr dom -> Σ -> dom

instance DomSem MInt where
  sem (Const a)    = \_ -> Just a
  sem (Var v)      = \σ -> Just $ σ v
  sem (Plus e1 e2) = \σ -> ((+)-^-) (sem e1 σ) (sem e2 σ)
  sem (Op e)       = \σ ->  (negate -^) (sem e σ)
  sem (Prod e1 e2) = \σ ->  ((*) -^-) (sem e1 σ)  (sem e2 σ)
  sem (Div e1 e2)  = \σ ->  if (sem e2 σ)  == Just 0
                              then Nothing
                              else ((div) -^-) (sem e1 σ)  (sem e2 σ)

instance DomSem MBool where
  sem (Eq e1 e2) = \σ -> ((==)-^-) (sem e1 σ) (sem e2 σ)
  sem (Lt e1 e2) = \σ -> ((<)-^-) (sem e1 σ) (sem e2 σ)
  sem (CBool b)  = \σ -> Just b
  sem (Not e)    = \σ -> (not -^) (sem e σ)
  sem (And e1 e2)= \σ -> ((&&) -^-) (sem e1 σ) (sem e2 σ)
  sem (Or e1 e2 )= \σ -> ((||) -^-) (sem e1 σ)  (sem e2 σ)
  sem (Gt e1 e2 )= \σ -> ((>) -^-) (sem e1 σ)  (sem e2 σ)
  sem (GtE e1 e2)= \σ -> ((>=) -^-) (sem e1 σ)  (sem e2 σ)
  sem (LtE e1 e2)= \σ -> ((<=) -^-) (sem e1 σ)  (sem e2 σ)

instance DomSem Ω where
  sem Skip           = \σ -> Normal σ
  sem (Assign v e)   = \σ -> (sem e σ, σ) >>== (\val -> Normal(update σ v val))                       -- v := e
  sem (Seq c1 c2)    = \σ -> ((sem c2) *.) (sem c1 σ)                                                 -- c ; c'
  sem (Cond b c1 c2) = \σ -> (sem b σ, σ) >>== (\bv -> if bv then sem c1 σ else sem c2 σ)             -- if b then c else c'
  sem (Newvar v e c) = \σ -> (sem e σ, σ) >>== (\val -> ((rest σ v) †.) (sem c (update σ v val)))     -- newvar v := e in e'
  sem (While b c)    = fix (f_big b c)                                                                -- while b do c
  -- # Comandos Fallas
  sem Fail           = \σ -> Abort σ                                                                  -- fail
  sem (Catch c1 c2)  = \σ -> ((sem c2) +.) (sem c1 σ)                                                 -- catch c with c'
  -- # Comandos IO
  sem (SOut e)       = \σ -> (sem e σ, σ) >>== (\val -> Out(val , Normal σ))                          -- !e
  sem (SIn  v)       = \σ -> In(\n -> Normal(update σ v n))                                           -- ?v



{- Funciones de evaluación de dom -}

class Eval dom where
  eval :: Expr dom -> Σ -> IO ()

instance Eval MInt where
  eval e = putStrLn . show . sem e

instance Eval MBool where
  eval e = putStrLn . show . sem e

instance Eval Ω where
  eval e = unrollOmega . sem e
    where unrollOmega :: Ω -> IO ()
          unrollOmega (Normal _)   = return ()
          unrollOmega (Abort _)    = putStrLn "Abort"
          unrollOmega (Out (n, ω)) = putStrLn (show n) >> unrollOmega ω
          unrollOmega (In f)       = getLine >>= unrollOmega . f . read

{-Ejemplo de uso de la semántica de evaluación-}

main = do
  eval (Prod (Const 5) (Const 3)) (\_ -> 0)
  eval (CBool True) (\_ -> 0)
  eval (Not (CBool False)) (\_ -> 0)
  eval (And (CBool True) (CBool False)) (\_ -> 0)
  eval (Eq (Const 3) (Const 4)) (\_ -> 0)
  eval (Eq (Div (Const 10) (Var "x")) (Const 5)) (\_ -> 0)
  eval (Eq (Div (Const 10) (Var "x")) (Const 5)) (\_ -> 2)

ej1 :: Expr Ω
ej1 = While (Lt (Var "x") (Const 10)) $
            Seq (SOut $ Var "x")
                (Assign "x" (Plus (Var "x") (Const 1)))


eval_ej1 :: IO ()
eval_ej1 = eval ej1 (\_ -> 0)


ej2 :: Expr Ω
ej2 = While (Lt (Var "y") (Const 10)) $
            Seq (Seq (Seq (SIn "x")
                          (SOut $ Var "x")
                     )
                     (SOut $ Var "y")
                )
                (Assign "y" (Plus (Var "y") (Const 1)))

eval_ej2 :: IO ()
eval_ej2 = eval ej2 (\_ -> 0)


ej3 :: Expr Ω
ej3 = Seq (Seq (SIn "x")
               (Newvar "x" (Const 10)
                       (SOut $ Var "x")
               )
          )
          (SOut $ Var "x")

eval_ej3 :: IO ()
eval_ej3 = eval ej3 (\_ -> 0)



-- Bucle Infinito
ej4 :: Expr Ω
ej4 = While (Gt (Var "x") (Op (Const 1))) $
            Seq (SOut $ Var "x")
                (Assign "x" (Plus (Var "x") (Const 1)))


eval_ej4 :: IO ()
eval_ej4 = eval ej4 (\_ -> 0)


ej5 :: Expr Ω
ej5 = Seq
        (SOut (Const 1))
        (Seq
          (Assign "x" (Const 10))
          (Seq
          (SOut (Var "x"))
          Fail))

eval_ej5 :: IO ()
eval_ej5 = eval ej5 (\_ -> 0)

ej6 :: Expr Ω
ej6 = Catch
  (Seq
    (SOut (Const 2))
    (Seq
      (Assign "x" (Const 99))
      (Seq
        (SOut (Var "x"))
         Fail)))
  (Seq
    (SOut (Const 42))
    (Assign "x" (Const 42)))

eval_ej6 :: IO ()
eval_ej6 = eval ej6 (\_ -> 0)

