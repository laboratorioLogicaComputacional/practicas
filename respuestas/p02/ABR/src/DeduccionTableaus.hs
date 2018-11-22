module DeduccionTableaus
--Verifica que una deduccion mediante un tableau sea correcta.
--mcb
where
import Data.List as L (delete,(\\)) -- (nub,union)
--import Data.Set as S
import SintaxisPL
--
--
---------------------------------------------------------------------------------------------------------------
-- Deduccion con tableaus:
-- Referencia: vanBenthem-vanEijck. Logic in Action, Capítulo 8. 2016 (disponible en el grupo)
--
--
-- Un tableau es un arbol.
-- Each node in the tree is called a sequent.
-- A tree of sequents is called a tableau.
-- A branch of such a tableau is closed if its end node contains a sequent
-- with a formula which appears both on the left (true) and on the right (false) part of the sequent.
--
-- As to distinguish open and closed branches
-- we replace the truth-falsity separation symbol ◦ by and • respectively.
--
data Tsequent   = Sep | Closed | Open --Tipo de "sequent": separacion, cerrado, abierto
                  deriving (Eq,Show)
type Sequent    = ([PL],Tsequent,[PL])

data ReglaT = --Reglas de reduccion para tableaus
              ConI | ConD   -- reglas para Conjuncion, izquierda y Derecha
            | DisI | DisD   -- reglas para Disyuncion, izquierda y Derecha
            | ImpI | ImpD   -- reglas para Implicacion, izquierda y Derecha
            | NegI | NegD   -- reglas para Negacion, izquierda y Derecha
            | EquI | EquD   -- reglas para Equivalencia, izquierda y Derecha
            deriving (Eq,Show)

data Tableau    =  -- Un tableau es un arbol de "sequents"
                  Hoja Sequent                              -- hoja de arbol (sin descendientes)
                | UnaRama  Sequent ReglaT Tableau           -- arbol de una rama
                | DosRamas Sequent ReglaT Tableau Tableau   -- arbol de dos ramas (izquierda y derecha)
                deriving (Eq,Show)

--
--
--
--Tableaus: -----------------------------------------------------------------------------
--
-- 1. Representar con una variable de tipo Tableau los dos tableaus de
-- la figura 8.1 (p.8-6) de vanBenthem-vanEijck. Logic in Action, Capítulo 8.
-- tFig8_1a :: Tableau
-- tFig8_1a = ...
-- tFig8_1b :: Tableau
-- tFig8_1b = ...
--
-- 2. Representar con una variable de tipo Tableau los dos tableaus de
-- la figura 8.2 (p.8-7) de vanBenthem-vanEijck. Logic in Action, Capítulo 8.
-- tFig8_2a :: Tableau
-- tFig8_2a = ...
-- tFig8_2b :: Tableau
-- tFig8_2b = ...
--
-- Definir una funcion, hojasDe, tal que: dado un tableau t, entregue una lista con las hojas de t.
--
hojasDe :: Tableau -> [Sequent]
hojasDe t = case t of
  Hoja s -> [s]
  UnaRama s r t -> hojasDe t
  DosRamas s r t1 t2 -> hojasDe t1 ++ hojasDe t2
-- Definir una funcion, rammasCerradas, tal que: dado un tableau t, regrese True sii todas las ramas de t están cerradas.
--
ramasCerradas :: Tableau -> Bool
ramasCerradas t = and [estaCerrado h | h <- hojasDe t]

-- Función auxiliar que nos indica si el sequent esta cerrado.
estaCerrado :: Sequent -> Bool
estaCerrado (t,_,f) = or [elem v f | v <- obtenAtomicas t]

-- Función que dada una lista de formulas nos regresa las formulas atomicas
obtenAtomicas :: [PL] -> [PL]
obtenAtomicas f = case f of
  [] -> []
  (l:ls) -> case l of
    Top -> [Top] ++ obtenAtomicas ls
    Bot -> [Bot] ++ obtenAtomicas ls
    Var n -> [Var n] ++ obtenAtomicas ls
    Oneg phi -> case phi of
      Var n -> [Oneg (Var n)] ++ obtenAtomicas ls
      _ -> obtenAtomicas ls
    _ -> obtenAtomicas ls
-- Definir una funcion, ramaAbierta, tal que: dado un tableau t, regrese True sii t tiene una rama abierta.
--
ramaAbierta :: Tableau -> Bool
ramaAbierta t = not (ramasCerradas t)
-- Definir una funcion, checkTableau, tal que: dado un tableau t, regresa True sii
-- todas las ramas de t estan construidas de acuerdo a la especificacion de la reglas de reduccion.
--
checkTableau :: Tableau -> Bool
checkTableau t = case t of
  -- Reglas para las hojas
  (Hoja s@(v, Closed, f)) -> estaCerrado s -- Si la hoja dice estar cerrada hay que verificarlo
  (Hoja s@(v, Open, f)) -> not (estaCerrado s) -- Si la hoja dice estar abierta hay que verificarlo
  -- Reglas para el conjunto de formulas de la izquierda
  -- Conjuncion Izquierda
  (UnaRama s@(v,ts,f) ConI t) -> ts == Sep && -- El seuquent no debe estar abierto o cerrado
                                 length v + 1 == length vh  && -- La lista resultante debe tener un elemento más ([Oand v1 v2], [v1, v2])
                                 conjFaltante cf avh && -- Verificamos que se elimino de manera correcta la conjunción
                                 checkTableau t -- Revisamos la rama
                                 where
                                   cf = elementosFaltantes v vh
                                   avh = conjPosibles (obtenAtomicas vh)
                                   vh = obtenListaIzquierda t

  -- Conjuncion Derecha
  (DosRamas s@(v,ts,f) ConD ti td) -> ts == Sep && -- El sequent no debe estar abierto o cerrado
                                      length f == length fhi && -- Verificamos que sean del mismo tamaño
                                      length f == length fhd && -- Verificamos que sean del mismo tamaño
                                      cfi == cfd && -- Verificamos que falten los mismo elementos
                                      elem a fhi && -- Verificamos que la primera parte de la conjuncion esta en la rama derecha
                                      elem b fhd && -- Verificamos que la segunda parte de la conjuncion esta en la rama derecha
                                      checkTableau ti && -- Revisamos la rama izquierda
                                      checkTableau td -- Revisamos la rama derecha
                                      where
                                        fhi = obtenListaDerecha ti
                                        fhd = obtenListaDerecha td
                                        cfi = elementosFaltantes f fhi
                                        cfd = elementosFaltantes f fhd
                                        c = cfi !! 0
                                        (a,b) = elementosCon c

  -- Disyunción Izquierda
  (DosRamas s@(v,ts,f) DisI ti td) -> ts == Sep && -- El sequent no debe estar abierto o cerrado
                                      length v == length vhi && -- Verificamos que sean del mismo tamaño
                                      length v == length vhd && -- Verificamos que sean del mismo tamaño
                                      dfi == dfd && -- Verificamos que falten los mismo elementos
                                      elem a vhi && -- Verificamos que la primera parte de la disyuncion esta en la rama izquierda
                                      elem b vhd && -- Verificamos que la segunda parte de la disyuncion esta en la rama derecha
                                      checkTableau ti && -- Revisamos la rama izquierda
                                      checkTableau td -- Revisamos la rama derecha
                                      where
                                        vhi = obtenListaIzquierda ti
                                        vhd = obtenListaIzquierda td
                                        dfi = elementosFaltantes v vhi
                                        dfd = elementosFaltantes v vhd
                                        d = dfi !! 0
                                        (a,b) = elementosDis d
  -- Disyunción Derecha
  (UnaRama s@(v,ts,f) DisD t) -> ts == Sep && -- El seuquent no debe estar abierto o cerrado
                                 length f + 1 == length fh  && -- La lista resultante debe tener un elemento más ([Oor v1 v2], [v1, v2])
                                 conjFaltante df afh && -- Verificamos que se elimino de manera correcta la disyuncion
                                 checkTableau t -- Revisamos la rama
                                 where
                                   df = elementosFaltantes f fh
                                   afh = conjPosibles (obtenAtomicas fh)
                                   fh = obtenListaDerecha t
  --Negacion Izquierda
  (UnaRama s@(v,ts,f) NegI t) -> ts == Sep && -- El seuquent no debe estar abierto o cerrado
                                 length f + 1 == length fh  && -- La lista resultante debe tener un elemento más ([Oneg v1 ], [v1])
                                 length v - 1 == length vh  && -- La lista resultante debe tener un elemento menos ([Oneg v1 ], [])
                                 conjFaltante dv afh && -- Verificamos que se elimino de manera correcta la negacion
                                 checkTableau t -- Revisamos la rama
                                 where
                                   afh = conjPosibles (obtenAtomicas fh)
                                   dv = elementosFaltantes v vh
                                   avh = conjPosibles (obtenAtomicas vh)
                                   vh = obtenListaIzquierda t
                                   fh = obtenListaDerecha t

  -- Negacion Derecha
  (UnaRama s@(v,ts,f) NegD t) -> ts == Sep && -- El seuquent no debe estar abierto o cerrado
                                 length v + 1 == length vh  && -- La lista resultante debe tener un elemento más ([Oneg v1 ], [v1])
                                 length f - 1 == length fh  && -- La lista resultante debe tener un elemento menos ([Oneg v1 ], [])
                                 conjFaltante dv avh && -- Verificamos que se elimino de manera correcta la negacion
                                 checkTableau t -- Revisamos la rama
                                 where
                                   dv = elementosFaltantes f fh
                                   avh = conjPosibles (obtenAtomicas fh)
                                   fh = obtenListaDerecha t
                                   vh = obtenListaIzquierda t

  --Implicacion izquierda
  (DosRamas s@(v,ts,f) ImpI ti td) -> ts == Sep && -- El seuquent no debe estar abierto o cerrado
                                      length v - 1 == length vh  && -- La lista resultante debe tener un elemento más ([Oneg v1 ], [v1])
                                      length f + 1 == length fh  && -- La lista resultante debe tener un elemento menos ([Oneg v1 ], [])
                                      conjFaltante dv avh && -- Verificamos que se elimino de manera correcta la negacion
                                      checkTableau ti && -- Revisamos la rama
                                      checkTableau td -- Revisamos la rama
                                      where
                                        dv = elementosFaltantes f fh
                                        avh = conjPosibles (obtenAtomicas fh)
                                        vh = obtenListaIzquierda t
                                        fh = obtenListaDerecha t

  --Implicacion derecha
  (UnaRama s@(v,ts,f) ImpD t) -> ts == Sep && -- El seuquent no debe estar abierto o cerrado
                                 length v + 1 == length vh  && -- La lista resultante debe tener un elemento más ([Oneg v1 ], [v1])
                                 length f - 1 == length fh  && -- La lista resultante debe tener un elemento menos ([Oneg v1 ], [])
                                 conjFaltante dv avh && -- Verificamos que se elimino de manera correcta la negacion
                                 checkTableau t -- Revisamos la rama
                                 where
                                   dv = elementosFaltantes f fh
                                   avh = conjPosibles (obtenAtomicas fh)
                                   vh = obtenListaIzquierda t
                                   fh = obtenListaDerecha t

  --Doble implicacion izquierda
  (DosRamas s@(v,ts,f) EquI ti td) -> ts == Sep && -- El seuquent no debe estar abierto o cerrado
								 length v + 1 == length vh  && -- La lista resultante debe tener un elemento más ([Oneg v1 ], [v1])
								 length f + 2 == length fh  && -- La lista resultante debe tener un elemento menos ([Oneg v1 ], [])
								 conjFaltante dv avh && -- Verificamos que se elimino de manera correcta la negacion
								 checkTableau ti && -- Revisamos la rama
								 checkTableau td -- Revisamos la rama
								 where
                   dv = elementosFaltantes f fh
                   avh = conjPosibles (obtenAtomicas fh)
                   vh = obtenListaIzquierda t
                   fh = obtenListaDerecha t

  --Doble implicacion Derecha
  (DosRamas s@(v,ts,f) EquD ti td) -> ts == Sep && -- El seuquent no debe estar abierto o cerrado
                                      length v + 1 == length vh  && -- La lista resultante debe tener un elemento más ([Oneg v1 ], [v1])
                                      length f + 2 == length fh  && -- La lista resultante debe tener un elemento menos ([Oneg v1 ], [])
                                      conjFaltante dv avh && -- Verificamos que se elimino de manera correcta la negacion
                                      checkTableau ti && -- Revisamos la rama
                                      checkTableau td -- Revisamos la rama
                                      where
                                        dv = elementosFaltantes f fh
                                        avh = conjPosibles (obtenAtomicas fh)
                                        vh = obtenListaIzquierda t
                                        fh = obtenListaDerecha t
-- Funciones auxiliares

-- Función que nos regresa la lista con las formulas verdaderas
obtenListaIzquierda :: Tableau -> [PL]
obtenListaIzquierda t = case t of
  Hoja s@(v,ts,f) -> v
  UnaRama s@(v,ts,f) r st -> v
  DosRamas s@(v,ts,f) r ti td -> v
  -- Función que nos regresa la lista con las formulas falsas
obtenListaDerecha :: Tableau -> [PL]
obtenListaDerecha t = case t of
  Hoja s@(v,ts,f) -> f
  UnaRama s@(v,ts,f) r st -> f
  DosRamas s@(v,ts,f) r ti td -> f

-- Función que nos regresa la lista con los elementos que estan en la primera y no en la segunda
elementosFaltantes :: [PL] -> [PL] -> [PL]
elementosFaltantes l1 l2 = l1 \\ l2

-- Función que nos dice las conjunciones posibles de una lista
conjPosibles :: [PL] -> [PL]
conjPosibles f = [Oand alpha beta | alpha <- f, beta <- f, alpha /= beta]

-- Función que nos dice si la conjunción fue eliminada correctamente
conjFaltante :: [PL] -> [PL] -> Bool
conjFaltante l1 l2 = length l1 == 1 &&
                     or [elem x l2 | x <- l1]
-- Función que nos regresa los elementos de una disyunción
elementosDis :: PL -> (PL,PL)
elementosDis phi = case phi of
  Oor alpha beta -> (alpha, beta)
  _ -> error $ "No es una disyuncion"
-- Función que nos regresa los elementos de una conjuncion
elementosCon :: PL -> (PL,PL)
elementosCon phi = case phi of
  Oand alpha beta -> (alpha, beta)
  _ -> error $ "No es una conjuncion"
