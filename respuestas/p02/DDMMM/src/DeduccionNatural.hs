module DeduccionNatural8 (ReglaDN(..), showCheckDedNat) 
--Verifica que los pasos de una deduccion natural sean correctos.
where
import Data.List as L (delete,(\\)) 
import SintaxisPL
--
--
---------------------------------------------------------------------------------------------------------------
-- Deduccion Natural:
--
data ReglaDN = 
              Icon  Int Int | Econ1 Int | Econ2 Int     -- reglas para la conjuncion
            | Iimp  Int Int | Eimp Int Int              -- reglas para la implicacion
            | Ineg  Int Int | Eneg Int Int              -- reglas para la negacion
            | Idis1 Int | Idis2 Int | Edis Int Int Int  -- reglas para la disyuncion
            | Ebot  Int -- regla para bottom (no hay introduccion de bottom)
            | Isup      -- regla para suposiciones (Assumptions). Las suposiciones se introducen con cajas en una prueba. 
            | Prem      -- ragla para premisas (premises). Las premisas se consideran validas en una prueba.
            | E2neg Int -- regla para eliminacion de doble negacion 
            | Itop      -- regla para top (no hay eliminacion de top). Esta regla no se usa.
            | Copy Int  -- Esta regla permite repetir una formula previa. Huth-Ryan p.20:
                -- The rule ‘copy’ allows us to repeat something that we know already. 
                -- We need to do this in this example, because the rule →i requires that we end the inner box with p. 
                -- The copy rule entitles us to copy formulas that appeared before,
                -- unless they depend on temporary assumptions whose box has already been closed. 
                -- Though a little inelegant, this additional rule is a small price to pay
                -- for the freedom of being able to use premises, or any other ‘visible’ formulas, more than once.            
            deriving (Eq,Show)
--
type Caja   = (Int,Int) -- Caja de suposiciones. Huth-Ryan p.12.
                        -- (i,j), 0<i<=j: caja cerrada de i a j
                        -- (i,j), 0=j<i : caja abierta de i a ...
            -- Proofs may nest boxes or open new boxes after old ones have been closed.
            -- There are rules about which formulas can be used at which points in the proof. 
            -- Generally, we can only use a formula φ in a proof at a given point if:
            --      (1) that formula occurs prior to that point and
            --      (2) no box which encloses that occurrence of φ has been closed already.
            -- The line immediately following a closed box has to match 
            -- the pattern of the conclusion of the rule that uses the box. 
            -- For implies-introduction, this means that we have to continue after the box with φ → ψ, 
            -- where φ was the first and ψ the last formula of that box.
--
type Paso   = (PL,ReglaDN,[Caja])   -- Un paso de una prueba, 
                                    -- (formula,regla_aplicada,listaDeCajas)
type NumPaso= (Int,Paso)            -- Un paso numerado, (numero, paso)
--
phiPasoNum :: Int->[NumPaso] -> PL
--formula del paso numero i en lpasos
phiPasoNum i lpasos = case mpi of
                    Just (fi,_,_) -> fi
                    _               -> error $ "phiPasoNum: i fuera de rango, (i,lpasos)="++show (i,lpasos)
    where
    mpi = lookup i lpasos
--
ultimoPaso :: [NumPaso] -> NumPaso 
ultimoPaso lpasos
    | lpasos /= [] = (n,p)
--     | otherwise = error $ "ultimoPaso: no hay pasos, lpasos="++show lpasos
    | otherwise = (0,(Top,Itop,[]))   -- (nN,(fN,r,lcN))
    where
    (n,p)   = last lpasos
--
eqCon1 :: PL -> PL -> Bool
-- True si g es el conyunto 1 de f
eqCon1 g f = case f of
              f1 `Oand` _   -> g == f1
              _             -> False
--
eqCon2 :: PL -> PL -> Bool
-- True si g es el conyunto 2 de f
eqCon2 g f = case f of
              _ `Oand` f2   -> g == f2
              _             -> False
--
usableP :: Int->[Caja]->Int -> Bool
-- True si el paso j es usable. Es decir, si 0<j<=nN y j no esta en ninguna caja cerrada.
usableP j lcajas nN =   0<j && j<=nN    -- j>0 y j es menor o igual que el ultimo paso previo
                    && and [not (k<=j && j<=l) | (k,l) <- cajasCerradas] -- j no está en ninguna caja cerrada.
                    where
                    cajasCerradas= [(k,l) | (k,l) <- lcajas, l/=0]
--
cerrarCaja :: [Caja]->Int->Int -> [Caja]
-- cierra correctamente la caja (i,0) de lcajas. 
cerrarCaja lcajas i j
    | (i,0) `notElem` cajasAbiertas     = error laCajaNoEstaAbierta
    | cajasInternasAbiertas /= []       = error hayUnaCajaInternaAbierta
    | j <= 0                            = error jDebeSerPositivo 
    | otherwise                         = (i,j): (L.delete (i,0) lcajas)
    where
    laCajaNoEstaAbierta     = "\n cerrarCaja: la caja "++show (i,j) ++" no esta abierta."
    hayUnaCajaInternaAbierta= "\n cerrarCaja: hay al menos una caja interna abierta: "++show (head cajasInternasAbiertas)
    jDebeSerPositivo        = "\n cerrarCaja: el final de la caja debe se positivo, j= "++show j
    cajasAbiertas           = [(k,l) | (k,l) <- lcajas, l==0]
    cajasInternasAbiertas   = [(k,l) | (k,l) <- cajasAbiertas, i<k]
--
esDisyuncion :: PL-> (Bool,PL,PL)
--Regresa (True,g,h) si f= g v h.
esDisyuncion f = case f of
                      g `Oor`h -> (True,g,h)
                      _         -> (False,Bot,Bot) 
--
checkPaso :: [PL]->[NumPaso]->NumPaso -> Bool
checkPaso lprem lpp p = -- listaDePremisas listaDePasosPrevios pasoActual
    case p of
         --Reglas para la conjuncion:
        (m,(g `Oand` h,Icon i j,lc)) -> lpp/=[]          -- hay pasos previos
                                        && m==nN+1          -- m se incrementa en 1.
                                        && lc== lcN         -- las cajas no cambiaron
                                        && usableP i lc nN  -- i es usable, i<nN && i no esta en una caja cerrada 
                                        && usableP j lc nN  -- j es usable, j<nN && j no esta en una caja cerrada 
                                        && g==fi && h==fj   -- introduccion de la conjuncion: fi,fj |- fi & fj
                                            where 
                                            fi= phiPasoNum i lpp -- paso i
                                            fj= phiPasoNum j lpp -- paso j
        (m,(g,Econ1 i,lc))           -> lpp/=[]          -- hay pasos previos
                                        && m==nN+1          -- m se incrementa en 1.
                                        && lc== lcN         -- las cajas no cambiaron
                                        && usableP i lc nN  -- i es usable, i<nN && i no esta en una caja cerrada 
                                        && g `eqCon1` fi    -- g es el conyunto 1 de fi: gi & hi |- gi
                                            where 
                                            fi = phiPasoNum i lpp -- paso i, fi= gi & hi
        (m,(h,Econ2 i,lc))           -> lpp/=[]          -- hay pasos previos
                                        && m==nN+1          -- m se incrementa en 1.
                                        && lc== lcN         -- las cajas no cambiaron
                                        && usableP i lc nN  -- i es usable, i<nN && i no esta en una caja cerrada 
                                        && h `eqCon2` fi    -- h es el conyunto 2 de fi: gi & hi |- hi
                                            where 
                                            fi = phiPasoNum i lpp -- paso i, fi= gi & hi
        --Reglas para la disyuncion:
        (m,(g `Oor` _, Idis1 i, lc)) -> lpp /= [] -- hay pasos previos
                                        && m==nN+1 -- m se incrementa en 1.
                                        && usableP i lcN nN -- i es usable, i<nN && i no esta en una caja cerrada
                                        && lc == lcN -- las cajas no cambiaron
                                        && g == fi
                                            where 
                                            fi = phiPasoNum i lpp
        (m,(_ `Oor` g, Idis2 i, lc)) -> lpp /= [] -- hay pasos previos
                                        && m==nN+1 -- m se incrementa en 1.
                                        && usableP i lcN nN -- i es usable, i<nN && i no esta en una caja cerrada
                                        && lc == lcN -- las cajas no cambiaron
                                        && g == fi
                                            where 
                                            fi = phiPasoNum i lpp
        (m,(w,Edis i j k,lc))       -> -- Eliminacion de la disyuncion: si fi=gvh, fj=g->w y fk=h->w, ent. fi,fj,fk |- w
                                        lpp/=[]            -- hay pasos previos
                                        && m==nN+1          -- m se incrementa en 1.
                                        && lc== lcN         -- las cajas no cambiaron
                                        && usableP i lc nN  -- i es usable, i<nN && i no esta en una caja cerrada 
                                        && usableP j lc nN  -- j es usable, j<nN && j no esta en una caja cerrada 
                                        && usableP k lc nN  -- k es usable, k<nN && k no esta en una caja cerrada 
                                        -- 
                                        && fiEsDisyuncion   -- fi= g`Oor`h
                                        && fj==(g`Oimp`w)   -- fj= g->w
                                        && fk==(h`Oimp`w)   -- fk= h->w  
                                            where 
                                            (fiEsDisyuncion,g,h) = esDisyuncion fi
                                            fi  = phiPasoNum i lpp -- paso i
                                            fj  = phiPasoNum j lpp -- paso j
                                            fk  = phiPasoNum k lpp -- paso k


        --Reglas para la implicacion:
        (m,(_ `Oimp` h,Iimp i j,lc)) -> lpp/=[]                  -- hay pasos previos
                                        && m==nN+1                  -- m se incrementa en 1.
                                        && j==nN && h==fN           -- h debe ser la del paso inmediato anterior.Huth-Ryan
                                        && lc L.\\ lcNijCerrada==[] -- se cerro la caja (i,j)
                                        && usableP i lcN nN -- i es usable, i<=nN && i no esta en una caja cerrada 
                                        && usableP j lcN nN -- j es usable, j<=nN && j no esta en una caja cerrada 
                                        && h==fj            -- introduccion de la implicacion: ...fj |- g->fj 
                                            where 
                                            lcNijCerrada= cerrarCaja lcN i j
                                            fj= phiPasoNum j lpp -- formula del paso j.
        (m,(h,Eimp i j,lc))          -> lpp/=[]          -- hay pasos previos
                                        && m==nN+1          -- m se incrementa en 1.
                                        && lc== lcN         -- las cajas no cambiaron
                                        && usableP i lc nN  -- i es usable, i<nN && i no esta en una caja cerrada 
                                        && usableP j lc nN  -- j es usable, j<nN && j no esta en una caja cerrada 
                                        && fj==fi `Oimp` h  -- eliminacion de la implicacion: fi,fi->h |- h
                                            where 
                                            fi= phiPasoNum i lpp -- paso i
                                            fj= phiPasoNum j lpp -- paso j
        --Reglas para la negacion (¬g = g -> Bot):
        (m,(Oneg _,Ineg i j,lc))     -> lpp/=[]                  -- hay pasos previos
                                        && m==nN+1                  -- m se incrementa en 1.
                                        && j==nN && Bot==fN         -- Bot debe ser la del paso inmediato anterior.Huth-Ryan
                                        && lc L.\\ lcNijCerrada==[] -- se cerro la caja (i,j)
                                        && usableP i lcN nN -- i es usable, i<=nN && i no esta en una caja cerrada 
                                        && usableP j lcN nN -- j es usable, j<=nN && j no esta en una caja cerrada 
                                        && Bot==fj  -- introduccion de la negacion: g...Bot |- g->Bot = ¬g
                                            where 
                                            lcNijCerrada= cerrarCaja lcN i j
                                            fj= phiPasoNum j lpp -- formula del paso j.
        (m,(Bot,Eneg i j,lc))        -> lpp/=[]              -- hay pasos previos
                                        && m==nN+1              -- m se incrementa en 1.
                                        && lc== lcN             -- las cajas no cambiaron
                                        && usableP i lc nN      -- i es usable, i<nN && i no esta en una caja cerrada 
                                        && usableP j lc nN      -- j es usable, j<nN && j no esta en una caja cerrada 
                                        && fj==fi `Oimp` Bot    -- eliminacion de la negacion: fi,fi->Bot |- Bot 
                                            where 
                                            fi= phiPasoNum i lpp -- paso i
                                            fj= phiPasoNum j lpp -- paso j

        (m,(phi,E2neg i,lc))       -> lpp/=[]
                                      && m == nN+1
                                      && lc == lcN
                                      && usableP i lc nN
                                      && fi == Oneg (Oneg phi)
                                          where 
                                          fi = phiPasoNum i lpp 
        -- Regla para suposiciones (Assumptions):
        (m,(_,Isup,lc))              -> m==nN+1                          -- m se incrementa en 1.
                                        && lc== lcN ++ [(nN+1,0)]           -- la caja (nN+1,0) se agrego a las cajas
        -- Regla para premisas (Premises):
        (m,(f,Prem,_))                -> f `elem` lprem   -- basta que f este en la lista de premisas
                                        && m==nN+1          -- m se incrementa en 1.
        -- Regla para Bot (no hay introduccion de Bot):
        (m,(_,Ebot i,lc))            -> lpp/=[]          -- hay pasos previos
                                        && m==nN+1          -- m se incrementa en 1.
                                        && lc== lcN         -- las cajas no cambiaron
                                        && usableP i lc nN  -- i es usable, i<nN && i no esta en una caja cerrada 
                                        && fi==Bot          -- eliminacion de Bot: Bot |- f
                                            where
                                            fi= phiPasoNum i lpp -- paso i
        -- Regla para Top:
        (m,(Top,Itop,_))              -> True -- Top se puede derivar sin restricciones
                                        && m==nN+1          -- m se incrementa en 1.
        -- Regla para usar formulas previas:
        (m,(f,Copy i,lc))            -> lpp/=[]          -- hay pasos previos
                                        && m==nN+1          -- m se incrementa en 1.
                                        && lc== lcN         -- las cajas no cambiaron
                                        && usableP i lcN nN -- i es usable, i<=nN && i no esta en una caja cerrada 
                                        && f== fi           -- f es la formula del paso i
                                            where 
                                            fi= phiPasoNum i lpp -- formula del paso i.
        _                               -> error $ "checkPaso: caso no implementado aun, p="++show p
        where
        (nN,(fN,_,lcN))= ultimoPaso lpp
--
--
checkPrueba :: [PL]->[NumPaso] -> Bool
-- True sii todos los pasos de lpasos son pasos válidos mediante alguna regla de deduccion natural.
checkPrueba lprem lpasos= -- listaDePremisas listaDePasos 
    case lpasos of
         []     -> True -- la lista de pasos vacia es valida
         _:_    -> checkPrueba lprem lpp && checkPaso lprem lpp p
         where
         n  = length lpasos
         lpp= Prelude.take (n-1) lpasos
         p  = last lpasos
--
---------------------------------------------------------------------------------------------------------------
--
showRegla :: ReglaDN->String
showRegla r= case r of
            -- reglas para la conjuncion:
            Icon  i j   -> "iCon "++show i++","++show j
            Econ1 i     -> "eCon1 "++show i
            Econ2 i     -> "eCon2 "++show i
            -- reglas para la implicacion:
            Iimp  i j   -> "iImp "++show i++"-"++show j
            Eimp i j    -> "eImp "++show i++","++show j
            -- reglas para la negacion:
            Ineg  i j   -> "iNeg "++show i++"-"++show j
            Eneg i j    -> "eNeg "++show i++","++show j
            -- reglas para la disyuncion:
            Idis1 i     -> "iDis1 "++show i
            Idis2 i     -> "iDis2 "++show i
            Edis i j k  -> "eDis "++show i++","++show j++","++show k
            -- regla para bottom (no hay introduccion de bottom):
            Ebot  i     -> "eBot "++show i
            -- regla para suposiciones (Assumptions):
            Isup        ->  "suposicion"
            -- regla para premisas (Premises):
            Prem        ->  "premisa"
            -- regla para eliminacion de la doble negacion:
            E2neg i     ->  "E¬¬ "++show i
            -- regla para top (no hay eliminacion de top). Esta regla no se usa:
            Itop        ->  "iTop"
            -- La siguiente regla permite repetir una formula previa. (***):
            Copy i      ->  "copy "++show i
--             _           ->  show r
            --
--
showLphi :: [PL] -> String
--Muestra una lista de formulas.
showLphi lphi= case lphi of
                    [f]     -> showPL f
                    f:lf    -> showPL f ++","++ showLphi lf
                    []      -> ""
--     
showCaja :: Caja -> String
showCaja (k,l) = showN k++"-"++ showN l
    where
    showN n= if n==0
                then "?"
                else show n
--
--
showLcajas :: [Caja] -> String
--Muestra una lista de cajas.
showLcajas lcajas= case lcajas of
                    [(i,j)] -> showCaja (i,j)
                    c:lc    -> showCaja c ++","++ showLcajas lc
                    []      -> ""
--
--                    
showNumPasoCheck :: Int->NumPaso->Bool -> String
-- Muestra un paso indicando, mediante b, si es correcto, o no.
showNumPasoCheck fSize (n,(f,r,lc)) b = "\t" ++ (show n) ++". "++ fS++ spaceAfterPhi++ rS ++ lcS  ++ checkS
    where
    fS              = showPL f
    spaceAfterPhi   = " " ++ Prelude.take (fSize-(length fS)) (repeat ' ')
    rS              = "\t " ++ (showRegla r)
    lcS             = ". Cajas=["++ showLcajas lc ++"]"
    checkS          = if b 
                        then ". Correcto" 
                        else ". Incorrecto"
--
showLpasos :: Int->[PL]->[NumPaso]->[NumPaso] -> IO ()
-- Muestra los pasos de lpasos indicando si son correctos, o no.
-- Initial call: showLpasos fSize lprem [] lpasos
showLpasos fSize lprem prevLp lpasos = 
    case lpasos of
            []      -> putStr ""
            p:lps   ->  do
                        putStrLn $ showNumPasoCheck fSize p (checkPaso lprem prevLp p)
                        showLpasos fSize lprem (prevLp++[p]) lps
--
--
showCheckConclusion :: [PL]->[NumPaso]->PL -> IO ()
showCheckConclusion lpremisas lpasos phi =   
    do
    putStrLn mensaje
    putStrLn ""
    where 
    mensaje 
        | not pruebaOK  = "\t*** Hay pasos incorrectos. ***"
        | lcAbiertas/=[]= "\t*** Hay cajas de suposiciones que no se cerraron ***: "++ showLcajas lcAbiertas
        | phi/=fN       = "\t*** La ultima fórmula no es el objetivo ***: "++ (showPL phi) ++" /= "++ (showPL fN)
        | otherwise     = "\tCorrecto. Mediante deduccion natural: "++ lpremS ++ " |- " ++ showPL fN
    pruebaOK            = checkPrueba lpremisas lpasos
    (_,(fN,_,lc))       = ultimoPaso lpasos
    lpremS              = if lpremisas /= []
                             then "{" ++ showLphi lpremisas ++"}"
                             else ""
    lcAbiertas          = [(i,j) | (i,j)<-lc, j==0]
--
maxL :: Ord a => [a] -> a
maxL = foldr1 (\x y ->if x >= y then x else y)
--
showCheckDedNat :: [PL]->[NumPaso]->PL -> IO ()
--Muestra y verifica que lpasos sea una deduccion natural correcta de: lpremisas |- phi.
--Es decir, muestra y verifica que lpasos es una prueba, con deduccion natural, de phi a partir de lpremisas.
showCheckDedNat lpremisas lpasos phi = --listaDePremisas listaDePasos
    do
    showLpasos fSize lpremisas [] lpasos
    showCheckConclusion lpremisas lpasos phi 
    where
    --fSize= 50
    fSize= maxL [length (showPL f) | (_,(f,_,_)) <- lpasos] 

