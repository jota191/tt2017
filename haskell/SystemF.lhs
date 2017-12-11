{-
  This program is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.
  
  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.
  
  You should have received a copy of the GNU General Public License
  along with this program.  If not, see <http://www.gnu.org/licenses/>.
-}


In this module some System F programs are encoded as an EDSL in haskell

> {-# LANGUAGE RankNTypes,
>              ScopedTypeVariables,
>              ExplicitForAll #-}

> module SystemF where
> import Prelude hiding (Bool, and, (+), (*),map)

Let the type of booleans be:

> type Bool = forall x. x -> x -> x

we define the values:

> tru :: Bool
> tru = \t f -> t

> fls :: Bool
> fls = \t f -> f

We define some fuctions, note that free variables on types
can be actually be closed by a forall quantifier on the left

> if₂ :: Bool -> a -> a -> a
> if₂ = \cond thn els -> cond thn els

> neg :: Bool -> Bool
> neg = \b -> b fls tru

> and :: Bool -> Bool -> Bool
> and = \l r -> l r fls

We can define more functions this way with no difficulty.
Let's go to more interesting stuff.

Naturals:


> type Nat = forall x. (x -> x) -> x -> x

> z :: Nat
> z = \f x -> x

> s :: Nat -> Nat
> s = \n f x -> f (n f x)  

< n3 = s $ s $ s $ z

With this representation we cannot print
values as they are represented, since they are functions.
There are many possible
solutions to this. For instane we can program a function of type
\mathbb{N} \to {\tt Int } (Haskell's Int type) and then print,
or directly apply SystemF values to a print function.

< n3 (\n -> n+1) 0 -- reduces to 3!

Let's define:

\begin{itemize}

\item Addition:

> (+) :: Nat -> Nat -> Nat
> (+) = \m n f x -> m f (n f x) 

\item Multiplication

> (*) :: Nat -> Nat -> Nat
> (*) = \m n f x -> m (n f) x 

\end{itemize}

Some constants

> n0  = z
> n1  = s $ z
> n2  = s $ n1
> n3  = s $ n2
> n5  = n2 + n3
> n10 = n5 + n2

Lists:

> type List a = forall x. x -> (a -> x -> x) -> x

> nil :: List a
> nil = \n c -> n

> cons :: forall a. a -> List a -> List a
> cons = \a l n c -> c a (l n c)  

> map :: forall a b.(a -> b) -> List a -> List b
> map = \f l n c -> l n (\v -> c (f v)) -- c.f
