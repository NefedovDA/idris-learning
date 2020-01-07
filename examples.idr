import Data.Vect
import Data.String

-- Супер фигня: ?rr, где rr - любое имя. Штуковина, которая имеет любой тип.
--    (читай, как `undefined` из Haskell, но может иметь разные имена)

-- Вспомогательная функция!
insert : Ord elem => (x : elem) -> (xs : Vect len elem) -> Vect (S len) elem
insert x [] = [x]
insert x ys@(y :: xs) = case x < y of
                          False => y :: insert x xs
                          True => x :: ys

-- Type classes как в Haskell указываются
insSort : Ord elem => Vect n elem -> Vect n elem
insSort [] = []
insSort (x :: xs) =
  let xs' = insSort xs
    in (insert x xs')

-- На самом деле тип функции: `zeroes : (n: Nat) -> Vect n Nat`,
--      но Idris нам помогает. Мы можем обратиться к 'скрытым' параметрам
--      через `{n = a}` или просто `{n}`, что эквивалентно `{n = n}`.
-- Pattern matching  работает и для скрытых переменных.
zeroes : Vect n Int
zeroes {n = Z} = []
zeroes {n = (S _)} = 0 :: zeroes

-- Ограниченный декримент
prev : Nat -> Nat
prev Z = 0
prev (S k) = k

-- `+`, как он есть в стандарной библиотеке.
-- Rem. Второй аргумент  сложения произвольное число,
--      а длину первого мы можем вывести из контекста.
--      (сколько раз применится рекурсия)
plus' : Nat -> Nat -> Nat
plus' Z j = j
plus' (S k) j = S (plus' k j)

-- Здравствуй, Idris!
-- Если написать в тупую: `.. = xs ++ [x]`,
--      он не сможет вывести соответствие чисел
-- (Ошибка: типы (S len) и (len + 1) не сходятся)
-- (len - длина xs, а 1 длина [x])
-- Поэтому мы извращяемся!
rotate : Vect n elem -> Vect n elem
rotate [] = []
rotate (x :: xs) = insLast x xs
  where
    insLast : a -> Vect k a -> Vect (S k) a
    insLast x [] = [x]
    insLast x (y :: xs) = y :: insLast x xs

-- Тут Idris нас заставляет обрабатывать возможные ошибки.
tryIndex : Integer -> Vect n a -> Maybe a
tryIndex {n} i xs = case integerToFin i n of
                         Nothing   => Nothing
                         (Just i') => Just (index i' xs)

-- А тут мы учимся указывать тип возвращаемого значения.
-- (`parsePositive : Num a => String -> Maybe a` - параметризованый тып
--      возвращаемого значения)
-- Вспомним, что `a` передаётся как скрытый параметр,
--      и `просто` передадим его :)
readNat : IO (Maybe Nat)
readNat = do s <- getLine
             pure (parsePositive {a = Nat} s)

-- Вызывающая сторона определяет длину,
--     а мы просим ввести ровно столько строк, сколько нужно.
readSpecVect : (len: Nat) -> IO (Vect len String)
readSpecVect Z = pure []
readSpecVect (S k) = do s <- getLine
                        ss <- readSpecVect k
                        pure (s :: ss)

-- Зависимая пара задаётся через `(A ** B)`.
-- Первый аргумет обязан быть типом! Он не передаётся как скрытый аргумент!
-- Тут уже сам пользователь определяет, когда он хочет закончить.
-- А мы, в свою очередь, вернём вектор нужной длины.
--
-- Немного ТТ:
-- Тут мы говорим, что ∃ len. (Vect len String)
--
readVect : IO (len ** Vect len String)
readVect = do s <- getLine
              if s == ""
                then pure (_ ** []) -- можно (0 ** []) или (0 ** _)
                else do (_ ** ss) <- readVect
                        pure (_ ** s :: ss) -- Rem. Первый аргумент Idris вычисляет сам.

filter' : (a -> Bool) -> Vect n a -> (m ** Vect m a)
filter' p xs = ?rr -- Упражнение ;)

-- Мы считали вектор `v1` и `v2`. Мы знаем их точный тип (длину в том числе).
-- Глянем на тип zip: `zip : Vect n a -> Vect n b -> Vect n (a, b)`
-- Ну можно проверить, что `l1` == `l2` и вызвать. Но нет!
-- Длины векторов мы узнаем только, когда их введёт нам пользователь,
--      а это Run Time. А проверка вызова функции - это Compile Time.
-- Сейчас для мы используем 'магическую' функцию exactLength,
--      которая проверит что длина вектора ровно `l1` и если так,
--      вернёт этот вектор, а иначе вернёт `Nothing`.
zipInputs : IO ()
zipInputs = do (l1 ** v1) <- readVect
               (l2 ** v2) <- readVect
               case exactLength l1 v2 of -- Волшебная функция! Потом узнаем как так делать.
                 Nothing  => putStrLn ("Error")
                 (Just v2') => printLn (zip v1 v2')

-- Начнём углубляться в типы

-- Rem. Забыл указать, как указывать типы. Вот так:
data MyType : Type -> Type -> Type where
  MyConstructor1 : String -> Int -> MyType String Int
  MyConstructor2 : String -> Int -> MyType String Int

-- Ещё примеры:
data MyBool : Type where
  MyTrue : MyBool
  MyFalse : MyBool

data MyPair : Type -> Type -> Type where
  MyMakePair : a -> b -> MyPair a b

-- Можно как в Haskell:
--      MyBool = MyTrue | MyFalse
--      MyPair = MyMakePair a b

-- End of Rem.

-- Типы и значения одно и тоже!
-- Аналогия: в функциональных языках мы спускаем функции до значений
--      и можем с ними работать. Тут мы ещё и типы спускаем.

-- Просто функция, которая возвращяет тип точки!
Position : Type
Position = (Double, Double)

-- Использование:
tri : Vect 3 Position
tri = [(0.0, 0.0), (0.0, 0.0), (0.0, 0.0)]

-- `Сложная` функция, конструирующая тип по данным аргументам
Poligon : Nat -> Type
Poligon n = Vect n Position

-- Смотри топ функции с типами
-- the : (a : Type) -> a -> a
--    the Int 5 |= 5 of type Int
-- cast : Cast from to => from -> to
--    the Int (cast "5") |= 5 of type Int
--    the - говорит какой тип должен вернуть cast
--    можно как раньше: cast {to=Int} "5"

data Ty = TyNat | TyBool | TyString

-- Фигня, которая помогает компилятору помогать писать код.
-- Можно забить..
%name Ty ty, ty1, ty2, ty3

-- Ну захотели мы отобразить наши типы в типы Idris.
evalType : Ty -> Type
evalType TyNat = Nat
evalType TyBool = Bool
evalType TyString = String

-- А тут по типу получаем дефолтное значение.
initVal : (ty: Ty) -> evalType ty
initVal TyNat = 0
initVal TyBool = False
initVal TyString = ""

-- Здесь наш тип кастуем в строку.
-- Нафига мы 3 раза написали одно и тоже?
-- Почему нельзя написать просто:
--    `toString ty x = show x`?
-- Ну на самом деле в такой реализации мы можем понять что за тип у `x`
--    с точки зрения типов Idris
toString : (ty: Ty) -> evalType ty -> String
toString TyNat x = show x
toString TyBool x = show x
toString TyString x = show x

-- Хотим функцию adder, которая умеет так:
--    adder 0 1       |= 1
--    adder 1 0 2     |= 1
--    adder 3 1 1 1 1 |= 4
-- Первый аргумент - сколько дополнительных аргументов
-- Второй аргумент - первое слагаемое
-- Остальные       - последующие слагаемые

-- Вроде, ничего особенного. Просто рекурсивный вывод типа. И в плюсах так можем.
--    Фи!
ExtraArgs : Nat -> (t: Type) -> Type
ExtraArgs Z     t = t
ExtraArgs (S k) t = t -> ExtraArgs k t

-- Помним, что считаную чиселки как количество доп аргументов передать не выйдет!
adder : Num a => (n : Nat) -> (acc: a) -> ExtraArgs n a
adder Z     acc = acc
adder (S k) acc = \i => adder k (acc + i) -- Должны вернуть функцию которая
                                          -- примет на 1 аргумент меньше
                                          -- и вернёт результат. Just do it!

-- Оппа! Домашка подъехало!
-- Кек, автор говорит, что это слишком сложнямба.
-- Смотри: /hw10/1.idr

-- Interfaces aka Type Classes from Haskell
-- Описывают поведение типа.

-- Конкретно:
--    `CollShow` говорит, что всякий тип, который хочет ему удовлетворять,
--    должен уметь круто показываться.
--    (К нему должна применяться функция `collShow`)
interface CoolShow a where
  coolShow : a -> String

-- Тут тип `Int` соглашается быть крутым.
-- Для этого он реализует функцию `coolShow`.
CoolShow Int where
  coolShow x = "!" ++ show x ++ "!"

-- Можно чуть длинее
implementation CoolShow MyBool where
  coolShow MyTrue = "(= Везуха =)"
  coolShow MyFalse = ")= Непруха =("

-- Можем повесить лейбл на свою реализацию функции
[myShowNat] Show Nat where
  show Z = "z"
  show (S k) = strCons 's' (show k)
-- Вызов: show @{myShowNat} (S (S (S Z)))
--    |= "sssz" : String

-- Можно контекст прокинуть внутрь любой функции!
f : Show a => a -> String
f x = "Result: " ++ show x
-- Вызов: f @{myShowNat} (the Nat 5)
--    |= "Result: sssssz" : String

-- Вот полугруппы я не понял :(
-- `Semigroup a` с операцией <+>
--      Видимо <+> - это операция на множестве,
--      которое мы объявим полугруппой относительно её.

-- Моноид - полугруппа с нейтральным эллементом!

-- Из стандартной библиотеки:
interface Functor' (f: Type -> Type) where
  -- Честные типы!
  map' : (m : a -> b) -> f a -> f b

plus_maybe : Maybe Nat -> Maybe Nat -> Maybe Nat
plus_maybe a b = [| a + b |]
-- Вот так раскроется: [| f a1 .. an |] -> pure f <*> a1 <*> ... <*> an
--
-- Можно так: plus_maybe a b = pure plus <*> a <*> b
-- Или так: plus_maybe a b = pure (!a + !b)
--      `!a` - эквивалентно: `va <- a` и использовать `va`


----- Пропуски
cong' : {f :  a -> b} -> x = y -> f x = f y
cong' Refl = Refl

---- Пропуски
data Parity : Nat -> Type where
  Even : Parity (n + n)
  Odd  : Parity (S (n + n))

proof_even : Parity ((S n) + (S n)) -> Parity (S (S (plus n n)))
proof_even {n} prf = rewrite plusSuccRightSucc n n in prf


proof_odd : Parity (S ((S n) + (S n))) -> Parity (S (S (S (plus n n))))
proof_odd {n} prf = rewrite plusSuccRightSucc n n in prf

parity : (n: Nat) -> Parity n
parity Z = Even {n = Z}
parity (S Z) = Odd {n = Z}
parity (S (S k)) with (parity k)
  parity (S (S (n + n))) | Even = proof_even (Even {n = S n})
  parity (S (S (S (n + n)))) | Odd = proof_odd (Odd {n = S n})
