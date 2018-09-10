module Practica1
where

data Natural = Cero | Suc Natural deriving (Eq, Show)

data ListaDeNaturales = Nil | Cons Natural ListaDeNaturales deriving (Eq, Show)

concate::ListaDeNaturales -> ListaDeNaturales -> ListaDeNaturales
concate l1 l2 = case l1 of
 Nil -> l2
 Cons n l -> Cons n (concate l l2)

reversa::ListaDeNaturales -> ListaDeNaturales
reversa l = case l of
 Nil -> Nil
 Cons n ls -> concate (reversa ls) (Cons n Nil)