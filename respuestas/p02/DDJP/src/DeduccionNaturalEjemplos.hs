module DeduccionNaturalEjemplos 
--Muestra ejemplos de la verificacion de deducciones naturales mediante showCheckDedNat.
where
import SintaxisPL
import DeduccionNatural (ReglaDN(..),showCheckDedNat)  
--
--
--
--
todosLosEjemplos :: IO ()
-- muestra todos los ejemplos.
todosLosEjemplos =
    do
    putStrLn ""
    putStrLn "Ejemplo thompsonP10:"
    thompsonP10
    --
    putStrLn "Ejemplo thompsonP12a:"
    thompsonP12a
    --
    putStrLn "Ejemplo thompsonP12b:"
    thompsonP12b
    --
    putStrLn "Ejemplo thompsonP12c1:"
    thompsonP12c1
    --
    putStrLn "Ejemplo huthRyanP20:"
    huthRyanP20
    --
    putStrLn "Ejemplo huthRyanP8Ej6:"
    huthRyanP8Ej6
    --
    putStrLn "Ejemplo thompsonP10:"
    thompsonP10
    --
    putStrLn "Ejemplo thompsonP12c2:"
    thompsonP12c2
    --
    
--
thompsonP10 :: IO ()
thompsonP10 = -- |- ((v1&v2)&v3) -> (v1&(v2&v3))
    let v1= Var 1
        v2= Var 2
        v3= Var 3
        gamma= []
        (∧) :: PL->PL->PL
        f∧g= Oand f g
        (⇒) :: PL->PL->PL
        f⇒g= Oimp f g
        lpasos= [   (1,((v1∧v2)∧v3,             Isup,       [(1,0)])), 
                (2,((v1∧v2),                    Econ1 1,    [(1,0)])), 
                (3,(v1,                         Econ1 2,    [(1,0)])), 
                (4,(v2,                         Econ2 2,    [(1,0)])), 
                (5,(v3,                         Econ2 1,    [(1,0)])), 
                (6,(v2∧v3,                      Icon 4 5,   [(1,0)])), 
                (7,(v1∧(v2∧v3),                 Icon 3 6,   [(1,0)])), 
                (8,(((v1∧v2)∧v3)⇒(v1∧(v2∧v3)),  Iimp 1 7,   [(1,7)]))
                ]
        phi= ((v1∧v2)∧v3)⇒(v1∧(v2∧v3))
    in showCheckDedNat gamma lpasos phi 
--
thompsonP12a :: IO ()
thompsonP12a = -- |- ((v1 ∧ v2) ⇒ v3) ⇒ (v1 ⇒ (v2 ⇒ v3))
    let v1= Var 1
        v2= Var 2
        v3= Var 3
        gamma= []
        (∧) :: PL->PL->PL
        f∧g= Oand f g
        (⇒) :: PL->PL->PL
        f⇒g= Oimp f g
        lpasos= [   (1,((v1∧v2)⇒v3,                 Isup,       [(1,0)])), 
                    (2,(v1,                         Isup,       [(1,0),(2,0)])), 
                    (3,(v2,                         Isup,       [(1,0),(2,0),(3,0)])), 
                    (4,(v1∧v2,                      Icon 2 3,   [(1,0),(2,0),(3,0)])), 
                    (5,((v1∧v2)⇒v3,                 Copy 1,     [(1,0),(2,0),(3,0)])), 
                    (6,(v3,                         Eimp 4 5,   [(1,0),(2,0),(3,0)])), 
                    (7,(v2 ⇒ v3,                    Iimp 3 6,   [(1,0),(2,0),(3,6)])), 
                    (8,(v1 ⇒(v2 ⇒ v3),              Iimp 2 7,   [(1,0),(2,7),(3,6)])),
                    (9,(((v1∧v2)⇒v3)⇒(v1⇒(v2⇒v3)),  Iimp 1 8,   [(1,8),(2,7),(3,6)])) 
                    ]
        phi= ((v1∧v2)⇒v3)⇒(v1⇒(v2⇒v3))
    in showCheckDedNat gamma lpasos phi
--
thompsonP12b :: IO ()
--  1. v1 Sup; 2. v1->v1 iImp 1-1. 
-- Huth-Ryan p.13:
-- The rule →i (with conclusion φ → ψ) does not prohibit the possibility that φ and ψ coincide. 
-- They could both be instantiated to p.
thompsonP12b  = -- |- v1->v1
    let 
        gamma   = []
        v1      = Var 1
        (⇒) :: PL->PL->PL
        f⇒g     = Oimp f g
        lpasos  = [ (1,(v1,     Isup,       [(1,0)])), 
                    (2,(v1⇒v1,  Iimp 1 1,   [(1,1)]))
                    ]
        phi     = v1⇒v1
    in showCheckDedNat gamma lpasos phi
--
thompsonP12c1 :: IO ()
-- 1. v2 Sup; 2. v1->v2 iImp 1-1; 3. v2->(v1->v2)
thompsonP12c1 = -- |- v2->(v1->v2) Incorrecta
    let v1= Var 1
        v2= Var 2
        gamma= []
        (⇒) :: PL->PL->PL
        f⇒g= Oimp f g
        lpasos = [  (1,(v2,             Isup,       [(1,0)])),  
                    (2,(v1⇒v2,          Iimp 1 1,   [(1,0)])), 
                    (3,(v2⇒(v1⇒v2),     Iimp 1 2,   [(1,1)])) 
                    ] 
        phi = v2⇒(v1⇒v2)
    in showCheckDedNat gamma lpasos phi 
    
    
--                
huthRyanP20 :: IO ()
huthRyanP20 = -- |- v2->(v1->v2) Correcta 
    let v1= Var 1
        v2= Var 2
        gamma= []
        (⇒) :: PL->PL->PL
        f⇒g= Oimp f g
        lpasos = [  (1,(v2,             Isup,       [(1,0)])), 
                    (2,(v1,             Isup,       [(1,0),(2,0)])), 
                    (3,(v2,             Copy 1,     [(1,0),(2,0)])), 
                    (4,(v1⇒v2,          Iimp 2 3,   [(1,0),(2,3)])), 
                    (5,(v2⇒(v1⇒v2),     Iimp 1 4,   [(1,4),(2,3)]))
                    ]
        phi = v2⇒(v1⇒v2)
    in showCheckDedNat gamma lpasos phi
--
--
huthRyanP8Ej6 :: IO ()
huthRyanP8Ej6 = -- {(v1 ∧ v2) ∧ v3, v4 ∧ v5} |− v2 ∧ v4
    let v1= Var 1
        v2= Var 2
        v3= Var 3
        v4= Var 4
        v5= Var 5
        gamma= [(v1∧v2)∧v3, v4∧v5]
        (∧) :: PL->PL->PL   -- ?
        f∧g= Oand f g       -- ?
        lpasos = [  (1,((v1∧v2)∧v3,     Prem,       [])), 
                    (2,(v4∧v5,          Prem,       [])), 
                    (3,(v1∧v2,          Econ1 1,    [])), 
                    (4,(v2,             Econ2 3,    [])),
                    (5,(v4,             Econ1 2,    [])), 
                    (6,(v2∧v4,          Icon 4 5,   []))
                    ]
        phi = v2∧v4
    in showCheckDedNat gamma lpasos phi 
    
    
------------
------------
ejemplo1 :: IO ()
ejemplo1 = -- |- --((v1 ⇒ v3) ∧ (v2 ⇒ v3)) ⇒ ((v1 ∨ v2) ⇒ v3)
    let v1= Var 1
        v2= Var 2
        v3= Var 3
        gamma = []
        (⇒) :: PL->PL->PL
        f⇒g= Oimp f g
        (∧) :: PL->PL->PL
        f∧g= Oand f g
        (∨) :: PL->PL->PL
        f∨g= Oor f g
        lpasos = [  (1,((v1⇒v2)∧(v2⇒v3),                                Isup,     [(1,0)])),
                    (2,((v1⇒v2,                                         Econ1 1,  [(1,0))),
                    (3,((v2⇒v3,                                         Econ2 1,  [(1,0))),
                    (4,((v1,                                            Isup,     [(1,0),(2,0)])),      
                    (5,((v2,                                            Eimp 2 4, [(1,0),(2,0)])),    
                    (6,((v3,                                            Eimp 3 5, [(1,0),(2,0)])),     
                    (7,((v1 ∨ v2,                                       Idis 4 5, [(1,0),(2,6)])), 
                    (8,((((v1 ∨ v2) ⇒ v3)                               Iimp 6 7, [(1,7),(2,6)])),         
                    (9,((((v1 ⇒ v3) ∧ (v2 ⇒ v3)) ⇒ ((v1 ∨ v2) ⇒ v3),    Iimp 7 8, [(1,7),(2,6)]))     
                    ]  
        phi = ((v1 ⇒ v3) ∧ (v2 ⇒ v3)) ⇒ ((v1 ∨ v2) ⇒ v3)
    in showCheckDedNat gamma lpasos phi 
    
    
ejemplo2 :: IO()
ejemplo2 = --  (v1 ⇒ v2), (v2 ⇒ v3) |− (v1 ⇒ v3)
    let v1= Var 1
        v2= Var 2
        v3= Var 3
        gama = [(v1 ⇒ v2), (v2 ⇒ v3)]
        (⇒) :: PL->PL->PL
        f⇒g= Oimp f g
        lpasos = [  (1,((v1 ⇒ v2),  Prem,       [])),
                    (2,((v2 ⇒ v3),  Prem,       [])),
                    (3,(v1,         Isup,       [(3,0)])),
                    (4,(v2,         Eimp 1 3,   [(3,0)])),
                    (5,(v3,         Eimp 1 4,   [(3,0)])),
                    (6,(v1 ⇒ v3,    Iimp 3 5,   [(3,5)]))
        ]
        phi = v1 ⇒ v3
    in showCheckDedNat gamma lpasos phi  
    
ejemplo3 :: IO ()
ejemplo3 = -- |− ((v1 ∨ v2) ⇒ v3) ⇒ ((v1 ⇒ v3) ∧ (v2 ⇒ v3))
    let v1= Var 1
        v2= Var 2
        v3= Var 3
        gama = []
        (⇒) :: PL->PL->PL
        f⇒g = Oimp f g
        (∧) :: PL->PL->PL
        f∧g = Oand f g
        (∨) :: PL->PL->PL
        f∨g = Oor f g
        lpasos = [  (1,((v1 ∨ v2) ⇒ v3),                            Isup,       [(1,0)])),
                    (2,(v1 ∨ v2,                                    Isup,       [(1,0),(2,0)])),
                    (3,(v3,                                         Eimp 1 2,   [(1,0),(2,0)])),
                    (4,(v1,                                         Isup,       [(1,0),(2,0),(3,0)])),
                    (5,(v3,                                         Copy 3,     [(1,0),(2,0),(3,0)])),
                    (6,(v1 ⇒ v3,                                    Iimp 4 5,   [(1,0),(2,0),(3,5)])),
                    (7,(v2,                                         Isup,       [(1,0),(2,0),(3,5),(7,0)])),
                    (8,(v3                                          Copy 3,     [(1,0),(2,0),(3,5),(7,0)])),
                    (9,(v2 ⇒ v3,                                    Iimp 7 8,   [(1,0),(2,0),(3,5),(7,8)])),
                    (10,((v1 ⇒ v3) ∧ (v2 ⇒ v3)                      Idis 6 9,   [(1,0),(2,9),(3,5),(7,8)])),
                    (11,(((v1 ∨ v2) ⇒ v3) ⇒ ((v1 ⇒ v3) ∧ (v2 ⇒ v3)),Iimp 1 10,  [(1,10),(2,9),(3,5),(7,8)]))
        ]
        phi = ((v1 ∨ v2) ⇒ v3) ⇒ ((v1 ⇒ v3) ∧ (v2 ⇒ v3))
    in showCheckDedNat gamma lpasos phi          
        
        
        
        
ejemplo4 :: IO ()
ejemplo4 = -- |− (v1 ⇒ (v2 ⇒ v3)) ⇒ ((v1 ∧ v2) ⇒ v3)
    let v1= Var 1
        v2= Var 2
        v3= Var 3
        gama = []
        (⇒) :: PL->PL->PL
        f⇒g = Oimp f g
        (∧) :: PL->PL->PL
        f∧g = Oand f g
        lpasos = [  (1,(v1 ⇒ (v2 ⇒ v3),                         Isup,       [(1,0)])),
                    (2,(v1,                                     Isup,       [(1,0),(2,0)])),
                    (3,(v2 ⇒ v3,                                Eimp 1 2,   [(1,0),(2,0)])),
                    (4,(v2,                                     Isup,       [(1,0),(2,0),(4,0)])),
                    (5,(v2 ⇒ v3,                                Copy 3,     [(1,0),(2,0),(4,0)])),
                    (6,(v3,                                     Eimp 4 5,   [(1,0),(2,0),(4,0)])),
                    (7,(v1,                                     Copy 2,     [(1,0),(2,0),(4,0)])),
                    (8,(v1 ∧ v2,                                Idis 4 7,   [(1,0),(2,0),(4,7)])),
                    (9,(v3,                                     Copy 6,     [(1,0),(2,0),(4,7)])), 
                    (10,((v1 ∧ v2) ⇒ v3,                        Iimp 8 9,   [(1,0),(2,9),(4,7)]))),
                    (11,((v1 ⇒ (v2 ⇒ v3)) ⇒ ((v1 ∧ v2) ⇒ v3),   Iimp 1 10,  [(1,10),(2,9),(4,7)]))       
        ]        
        phi = (v1 ⇒ (v2 ⇒ v3)) ⇒ ((v1 ∧ v2) ⇒ v3)
    in showCheckDedNat gamma lpasos phi           
        
        
ejemplo5 :: IO ()
ejemplo5 = -- |− (v1 ⇒ v2) ⇒ (v2 ⇒ v1)
    let v1= Var 1
        v2= Var 2
        gama = []
        (⇒) :: PL->PL->PL
        f⇒g = Oimp f g
        lpasos = [  (1,(v1 ⇒ v2,                Isup,       [(1,0)])),
                    (2,(v1,                     Isup,       [(1,0),(2,0)])),
                    (3,(v2,                     Eimp 1 2,   [(1,0),(2,0)])),
                    (4,(v2 ⇒ v1,                Iimp 2 3,   [(1,0),(2,3)])),
                    (5,((v1 ⇒ v2) ⇒ (v2 ⇒ v1),  Iimp 1 4,   [(1,4),(2,3)]))
        ]        
        phi = (v1 ⇒ v2) ⇒ (v2 ⇒ v1)
    in showCheckDedNat gamma lpasos phi          
        
        
        
        
ejemplo6 :: IO ()
ejemplo6 = -- |− v
    let v1= Var 1
        gama = []
        (¬) :: PL -> PL
        ¬f = Oneg f
        (⇒) :: PL->PL->PL
        f⇒g = Oimp f g
        lpasos = [  (1,(v1,             Isup,       [(1,0)])),
                    (2,(¬v1,            Isup,       [(1,0),(2,0)])),
                    (3,(Bot,            Eneg 1 2,   [(1,0),(2,0)])),
                    (4,(¬(¬v1),         Ineg 2 3,   [(1,0),(2,3)])),
                    (5,(v1 ⇒ (¬(¬v1))   Iimp 1 4,   [(1,4),(2,3)]))
        ]    
        phi = v1 ⇒ (¬(¬v1))
    in showCheckDedNat gamma lpasos phi      
    

ejemplo7 :: IO ()
ejemplo7 = -- |- ((v1⇒v2)⇒v1)⇒v1
    let v1= Var 1
        v2= Var 2
        gamma= []
        (⇒) :: PL->PL->PL
        f⇒g= Oimp f g
        lpasos = [  (1,(v1,                 Isup,       [(1,0)])), 
                    (2,(v2,                 Isup,       [(1,0),(2,0)])), 
                    (3,(v1,                 Copy 1,     [(1,0),(2,0)])), 
                    (4,(v1⇒v2,              Iimp 2 3,   [(1,0),(2,3)])), 
                    (5,((v1⇒v2)⇒v1,         Iimp 1 4,   [(1,0),(2,3)])),
                    (6,(((v1⇒v2)⇒v1)⇒v1,    Iimp 1 5,   [(1,5),(2,3)])),                   
                    ]
        phi = ((v1⇒v2)⇒v1)⇒v1
    in showCheckDedNat gamma lpasos phi

