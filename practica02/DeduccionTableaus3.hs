module DeduccionTableaus3 (ramasCerradas,ramaAbierta,checkTableau,impLogicaConTableaus)
--Verifica que una deduccion mediante un tableau sea correcta.
--mcb
where
import Data.List as L ((\\),intersect) -- (delete,nub,union)
import Data.Set as S (fromList)
import SintaxisPL
--
--
---------------------------------------------------------------------------------------------------------------
-- Deduccion con tableaus:
-- Referencia: vanBenthem-vanEijck. Logic in Action, Capítulo 8. 2016 (disponible en el grupo)
--
--
-- Un tableau es un arbol.
-- Each node in the tree is called a sequent. (Separation symbol: ◦, left: truth, right: falsity).
-- A tree of sequents is called a tableau. 
--
-- A branch of such a tableau is closed if its end node contains a sequent 
-- with a formula which appears both on the left (true) and on the right (false) part of the sequent.
-- If all branches are closed then the tableau is also closed, 
-- and it says that the top-sequent represents in fact a valid inference. 
--
-- A branch of a tableau is called open if its final node is not closed and contains no logical symbols. 
-- In this case we have found a counter-example since there are only propositional letters left. 
-- A valuation which assigns the value 1 to all the proposition letters on the left part, 
-- and 0 to those on the right side will be a counter-model for the inference with which you started the tableau. 
--
-- As to distinguish open and closed branches 
-- we replace the truth-falsity separation symbol ◦ (Sep) by _(Open) and •(Closed) respectively.
--
data Tsequent   = Sep | Closed | Open --Tipo de "sequent": separacion, cerrado, abierto
                  deriving (Eq,Show)
type Sequent    = ([PL],Tsequent,[PL])     

data ReglaR = --Reglas de reduccion para tableaus
              ConI | ConD   -- reglas para Conjuncion, izquierda y Derecha
            | DisI | DisD   -- reglas para Disyuncion, izquierda y Derecha
            | ImpI | ImpD   -- reglas para Implicacion, izquierda y Derecha
            | NegI | NegD   -- reglas para Negacion, izquierda y Derecha
            | EquI | EquD   -- reglas para Equivalencia, izquierda y Derecha
            deriving (Eq,Show)

type ReglaT = (ReglaR,PL) -- (ReglaDeReduccion, FormulaAlaQueSeAplicaLaRegla)
    
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
-- Regresa una lista con las hojas de t 
hojasDe t = case t of
    Hoja s                -> [s]
    UnaRama  _ _ t1       -> hojasDe t1
    DosRamas _ _ t1 t2    -> hojasDe t1 ++ hojasDe t2
--    
-- Definir una funcion, rammasCerradas, tal que: dado un tableau t, regrese True sii todas las ramas de t están cerradas.
--
ramasCerradas :: Tableau -> Bool
-- Regresa True sii todas las ramas de t están cerradas
ramasCerradas t = and [estaCerrado h | h <- hojasDe t]
--
-- Definir una funcion, ramaAbierta, tal que: dado un tableau t, regrese True sii t tiene una rama abierta.
--
ramaAbierta :: Tableau -> Bool
-- Regresa True sii todas las ramas de t tiene una rama abierta
ramaAbierta t = not (ramasCerradas t)
--
estaCerrado :: Sequent -> Bool
-- True si el sequent esta cerrado.
-- A sequent with a formula which appears both on the left (true) and on the right (false) part.
estaCerrado (t,_,f) = t `intersect` f /= []
--
estaAbierto :: Sequent -> Bool
-- A node that is not closed and contains no logical symbols. 
estaAbierto s = (not $ estaCerrado s) && noLogicalSymbols s
--
esDeSeparacion :: Sequent -> Bool
-- Un node es de separacion si no es cerrado y no es abierto.
esDeSeparacion s= not(estaCerrado s) && not(estaAbierto s)
--
esAtomica :: PL -> Bool
--True si phi es atomica (no tiene simbolos logicos)
esAtomica phi= case phi of
                    Top     -> True
                    Bot     -> True
                    Var _   -> True
                    _       -> False
--
noLogicalSymbols :: Sequent -> Bool
-- True si todas las formulas del secuente no tienen simbolos logicos (i.e. son formulas atomicas)
noLogicalSymbols (t,_,f)= and [esAtomica phi | phi <- t++f]
--
secuenteDeRaiz :: Tableau -> ([PL],[PL])
--Regresa el secuente de la raiz de un tableau.
secuenteDeRaiz t = case t of
                        Hoja (v,_,f)           -> (v,f)
                        UnaRama (v,_,f) _ _    -> (v,f)
                        DosRamas (v,_,f) _ _ _ -> (v,f)
--
eqLists :: [PL]->[PL]-> Bool
-- True si l1 y l2 son lista iguales vistas como conjuntos.
eqLists l1 l2 = S.fromList l1 == S.fromList l2
--
checkTableau :: Tableau -> Bool
-- Dado un tableau t, regresa True sii
-- todas las ramas de t estan construidas de acuerdo a la especificacion de la reglas para los tableaus.
checkTableau t = case t of
    -- Reglas para las hojas
    Hoja s@(_, Closed, _)           -> estaCerrado s    -- Las hojas con secuente "Closed" deben estar cerradas
    Hoja s@(_, Open, _)             -> estaAbierto s    -- Las hojas con secuente "Open" deben estar abiertas
    Hoja s@(_,Sep,_)                -> esDeSeparacion s -- Las hojas con secuente "Sep" deben ser de separacion.
    -- Reglas con UNA rama:
    UnaRama (v,ts,f) regla t1       -> 
        case regla of
            (ConI,phi)  -> -- g&h=1 sii g,h=1
                        case phi of
                          Oand g h     -> ts == Sep    -- El secuente no debe estar abierto o cerrado
                                        && phi `elem` v -- phi debe estar en el secuente izq.
                                        && v1 `eqLists` ((v\\[phi])++[g,h]) -- v1= consecuencia(regla).
                                        && f1 `eqLists` f                   -- f1= consecuencia(regla).
                                        && checkTableau t1 -- Revisamos recursivamente t1
                                        
                          _           -> False -- phi debe ser una conjuncion
            (DisD,phi)  ->
                        case phi of
                          Oor g h      -> ts == Sep    -- El secuente no debe estar abierto o cerrado
                                        && phi `elem` f -- phi debe estar en el secuente der.
                                        && f1 `eqLists` ((f\\[phi])++[g,h]) -- f1= consecuencia(regla)
                                        && v1 `eqLists` v                   -- v1= consecuencia(regla)
                                        && checkTableau t1 -- Revisamos recursivamente t1
                                        
                          _             -> False -- phi debe ser una disyuncion
            (ImpD,phi)  ->
                        case phi of
                          Oimp g h     -> ts == Sep    -- El secuente no debe estar abierto o cerrado
                                        && phi `elem` f -- phi debe estar en el secuente der.
                                        && v1 `eqLists` (v++[g])          -- v1= consecuencia(regla)
                                        && f1 `eqLists` ((f\\[phi])++[h]) -- f1= consecuencia(regla)
                                        && checkTableau t1 --Revisamos recursivamente t1
                                        
                          _             -> False -- phi debe ser una implicacion
            (NegI,phi)  ->
                        case phi of
                          Oneg(g)      -> ts == Sep    -- El secuente no debe estar abierto o cerrado
                                        && phi `elem` v -- phi debe estar en el secuente izq. 
                                        && v1 `eqLists` (v\\[phi])   -- v1= consecuencia(regla)
                                        && f1 `eqLists` (f++[g]) -- f1= consecuencia(regla)
                                        && checkTableau t1 -- Revisamos recursivamente t1
                                        
                          _             -> False -- phi debe ser una formula negada
            (NegD,phi)  ->
                        case phi of
                          Oneg(g)      -> ts == Sep    -- El secuente no debe estar abierto o cerrado
                                        && phi `elem` f -- phi debe estar en el secuente der. 
                                        && v1 `eqLists` (v++[g])   -- v1= consecuencia(regla)
                                        && f1 `eqLists` (f\\[phi]) -- f1= consecuencia(regla)
                                        && checkTableau t1 -- Revisamos recursivamente t1
                                        
                          _             -> False -- phi debe ser una formula negada      
            _           -> False -- No hay mas reglas que produzcan una rama
        where 
        (v1,f1)= secuenteDeRaiz t1 -- secuente de la raiz de t1
    -- Reglas con DOS ramas:
    DosRamas (v,ts,f) regla ti td   -> 
        case regla of
            (DisI,phi)  -> -- g|h=1 sii g=1 o h=1 
                        case phi of
                            Oor g h   -> ts == Sep     -- El secuente no debe estar abierto o cerrado
                                        && phi `elem` v -- phi debe estar en el secuente izq.
                                        && vI `eqLists` ((v\\[phi])++[g]) -- vI= consecuencia(regla).
                                        && fI `eqLists` f                 -- fI= consecuencia(regla).
                                        && vD `eqLists` ((v\\[phi])++[h]) -- vD= consecuencia(regla).
                                        && fD `eqLists` f                 -- fD= consecuencia(regla).
                                        && checkTableau ti -- Revisamos recursivamente ti
                                        && checkTableau td -- Revisamos recursivamente td
                            _           -> False -- phi debe ser una disyuncion
            (ConD,phi)  ->
                        case phi of
                            Oand g h  -> ts == Sep     -- El secuente no debe estar abierto o cerrado
                                        && phi `elem` f -- phi debe estar en el secuente izq.
                                        && vI `eqLists` v
                                        && fI `eqLists` ((f\\[phi])++[g])
                                        && vD `eqLists` v
                                        && fD `eqLists` ((f\\[phi])++[h])
                                        && checkTableau ti -- Revisamos recursivamente ti
                                        && checkTableau td -- Revisamos recursivamente td
                            _           -> False -- phi debe ser una disyuncion

            (ImpI,phi)  -> error $ "Regla no implementada aun: "++show (ImpI,phi)
            (EquI,phi)  -> error $ "Regla no implementada aun: "++show (EquI,phi)
            (EquD,phi)  -> error $ "Regla no implementada aun: "++show (EquD,phi)
            _           -> False -- No hay mas reglas que produzcan dos ramas
        where 
        (vI,fI)= secuenteDeRaiz ti -- secuente de la raiz de ti
        (vD,fD)= secuenteDeRaiz td -- secuente de la raiz de td
--
impLogicaConTableaus :: [PL]->PL->Tableau -> Bool
-- Implicacion logica usando tableaus.
-- Regresa True si t es un tableau que demuestra que cGamma implica logicamente a phi, Gamma |= phi.
impLogicaConTableaus cGamma phi t = 
       v `eqLists` cGamma   -- el lado izq de raiz(t) es cGamma
    && f == [phi]           -- el lado der de raiz(t) es [phi]
    && checkTableau t       -- el tableau esta construido de acuerdo a las reglas de reduccion
    && ramasCerradas t      -- todas las ramas de t estan cerradas
    where
    (v,f)= secuenteDeRaiz t -- secuente de la raiz de t
--    
--
