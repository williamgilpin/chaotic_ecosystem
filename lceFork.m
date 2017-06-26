(* ::Package:: *)

(* :Copyright: Copyright 1995 Marco Sandri *)

(* :Name: LCE` *)

(* :Title: Numerical Calculation of Lyapunov Characteristic
Exponents for Smooth Dynamical Systems *)

(* :Author: 
        Marco Sandri
        IULM University
        Facolt\:0824i Arti, mercati e patrimoni della cultura
        Istituto di Arti, culture e letterature comparate        
        Via Carlo Bo, 1
        20143 Milano - Italy 
        Email: sandri.marco@gmail.com 
        Web: http://www.msandri.it *)

(* :Summary: *)

(* :Package Version: Mathematica 7.0 *)

(* :History: *)

(* :Keywords: Discrete and Continuous Dynamical Systems, Ergodic
Theory, Chaos, Lyapunov Exponents. *)

(* :Source:
    Benettin G., Galgani L., Giorgilli A. and Strelcyn J.M. (1980)
    "Lyapunov Characteristic Exponents for Smooth Dynamical
    Systems and for Hamiltonian Systems. A Method for Computing
    All of Them. Part 2. Numerical Application."
    Meccanica 15, 21-30.

    Eckmann J.P. and Ruelle D. (1985)
    "Ergodic Theory of Chaos and Strange Attractors"
    Review of Modern Physics, Vol. 57, No. 3, Part 1.

    Parker T.S. and Chua L.O. (1989)
    "Practical Numerical Algorithms for Chaotic Systems"
    Springer-Verlag, New York. 
    
    Maeder, R.E. 1991. Programming in Mathematica. 2nd ed. 
    pp. 171-175. Addison-Wesley.

    *)

(* :Limitation: *)

BeginPackage["LCE`"] (* , "LinearAlgebra`Orthogonalization`"] *)


LCEsC::usage=
"LCEsC[flist, xxx0, T, K, TR, stepsize, opts] computes the Lyapunov spectrum and
dimension of a given continuous-time dynamical system flist with starting initial
condition xxx0, for T seconds and K steps, excluding the transient for TR steps. If
LCEsPlot -> True option is specified, then LCEsC plots the entire spectrum."

LCEsD::usage=
"LCEsD[flist,  xxx0, N, TR, opts] computes the Lyapunov spectrum and dimension of a
given discrete-time dynamical system flist with starting initial condition xxx0,
for a given number N of iterates, excluding the transient for TR steps. If
LCEsPlot -> True option is specified, then LCEsC plots the entire spectrum."

LCEsPlot::usage=
"LCEsPlot is an option of the LCEsD and LCEsC commands. If LCEsPlot -> True 
option is specified, the Lyapunov spectrum is plotted."

PhaseSpaceC::usage=
"PhaseSpaceC[flist, xxx0, T, TR, stepsize, pattern] plots in the (2D or 3D)
phase-space the orbit of a given continuous-time dynamical system flist with
starting initial condition xxx0, for T seconds, excluding the transient for TR
steps. Setting pattern={i,j,k} (for dimensions >=3 only) variables ai,aj,ak
are plotted on the xxx,yyy,zzz axes respectively."

PhaseSpaceD::usage=
"PhaseSpaceD[flist, xxx0, T, TR, pattern] plots in the (2D or 3D) phase-space the
orbit of a given discrete-time dynamical system flist with starting initial
condition xxx0, for T iterates, excluding the transient for TR steps. Setting 
pattern={i,j,k} (for dimensions >=3 only) variables ai,aj,ak are plotted on 
the xxx,yyy,zzz axes respectively."

ConvergencePlot::usage =
"ConvergencePlot[lces] plots the convergence of the LCEs."

LyapunovDimension::usage = 
"LyapunovDimension[lceslist] calculates the Lyapunov dimension of the 
attractor, given the Lyapunov spectrum lceslist."

RKPoint::usage = 
"RKPoint[{e1,e2,..}, {yyy1,yyy2,..}, {a1,a2,..}, {t1, dt}] numerically integrates the
ei as functions of the yyyi with initial values ai, giving as result the final
state of the dynamical system."

RKList::usage = 
"RKList[{e1,e2,..}, {yyy1,yyy2,..}, {a1,a2,..}, {t1, dt}] numerically integrates the
ei as functions of the yyyi with initial values ai, giving as result the orbit of
the dynamical system."

IntVarEq::usage = 
"IntVarEq[F, DPhi, xxx, Phi, xxx0, Phi0, {t1, dt}] numerically integrates the 
variational equation defined in [Parker and Chua 1989, 305-306]."

LCE::pos = 
"The sum of the LCEs must be less than or equal to zero.";

Options[LCEsD] = {LCEsPlot -> False};
Options[LCEsC] = {LCEsPlot -> False};

(*==============================================================*)

(*Begin["`Private`"]*)

(*==============================================================*)
JacobianMtx[funs_List, vars_List] := Outer[D, funs, vars]

RKStep[f_, yyy_, yyy0_, dt_] :=
Module[{ kkk1, kkk2, kkk3, kkk4 },
    kkk1 = dt N[ f /. Thread[yyy -> yyy0] ];
    kkk2 = dt N[ f /. Thread[yyy -> yyy0 + kkk1/2] ];
    kkk3 = dt N[ f /. Thread[yyy -> yyy0 + kkk2/2] ];
    kkk4 = dt N[ f /. Thread[yyy -> yyy0 + kkk3] ];
    yyy0 + (kkk1 + 2 kkk2 + 2 kkk3 + kkk4)/6 ]

RKPoint[f_List, yyy_List, yyy0_List, {t1_, dt_}] :=
    Nest[ RKStep[f, yyy, #, N[dt]]&, N[yyy0], Round[N[t1/dt]] ]

RKList[f_List, yyy_List, yyy0_List, {t1_, dt_}] :=
    NestList[ RKStep[f, yyy, #, N[dt]]&, N[yyy0], Round[N[t1/dt]] ]

IntVarEq[F_List, DPhi_List, xxx_List, Phi_List, xxx0_List, 
        Phi0_List, {t1_, dt_}] :=
Module[{n, f, yyy, yyy0, yyyt},
    n = Length[xxx0];
    f = Flatten[Join[F, DPhi]];
    yyy = Flatten[Join[xxx, Phi]];
    yyy0 = Flatten[Join[xxx0, Phi0]];
    yyyt = Nest[ RKStep[f, yyy, #, N[dt]]&, N[yyy0], Round[N[t1/dt]] ];
    {First[#], Rest[#]}& @ Partition[yyyt, n] ]

LyapunovDimension[xxx_] :=
Module[{l, suml, j},
    l = Sort[xxx, Greater];
    suml = Rest[FoldList[Plus, 0, l]];
    If[Last[suml] > 0, Message[LCE::pos]; Return[$Failed] ];
    j = Last[Position[suml, _?Positive]];
    First[j - suml[[j]]/l[[j+1]]] ]

ConvergencePlot[xxx_List] := Show[
    Map[ListPlot[#, Joined -> True,
            DisplayFunction -> Identity, PlotRange -> All]&, 
        Transpose[xxx] ],
    Frame -> True, FrameLabel -> {"Steps", "LCEs"},
    DisplayFunction -> $DisplayFunction]

LCEsC[f_, initcond_, T_, K_, trans_:0, stepsize_:0.02, opts___Rule] :=
Module[{opt, n, a, b, xxx, xxx0, Phi, DPhi, V0, s, 
            W, norms, lcelist, lces},  
    opt = LCEsPlot /. {opts} /. Options[LCEsC];
    n = Length[initcond];
    xxx = Array[a, n];
    Phi = Transpose[Array[b, {n, n}]];
    DPhi = Phi.Transpose[JacobianMtx[f[xxx], xxx]];
    xxx0 = Nest[RKStep[f[xxx], xxx, #, N[stepsize]]&, N[initcond],
         Round[N[trans/stepsize]] ];
    V0 = IdentityMatrix[n];
    s = {};
    Do[
      {xxx0, V0} = IntVarEq[f[xxx], DPhi, xxx, Phi, xxx0, V0, {T, stepsize}];
      W = GramSchm[V0];
      norms = Map[Norm, W];
      s = Append[s, norms];
      V0 = W/norms,
      {K}];    
    If[opt,
      lcelist = Rest[FoldList[Plus, 0, Log[s]]]/(T Range[K]);
      Return[ConvergencePlot[lcelist] ],
      lces = Sort[Apply[Plus, Log[s]]/(T K), Greater];
      Return[{lces, LyapunovDimension[lces]}]
    ];  
  ]



LCEsD[f_, initcond_, K_, trans_:0, opts___Rule] :=
Module[{opt, n, a, J, s, q, r, lces},
    opt = LCEsPlot /. {opts} /. Options[LCEsD];
    n = Length[initcond];
    xxx = Array[a, n];
    J[yyy_List] := JacobianMtx[f[xxx], xxx] /. Thread[xxx -> yyy];
    xxx0 = Nest[f, N[initcond], trans];
    {q, r} = QRDecomposition[J[xxx0]];
    s = {};    
    Do[
      xxx0 = f[xxx0];
      {q, r} = QRDecomposition[J[xxx0].Transpose[q]];
      s = Append[s, Table[r[[i,i]], {i, n}]],
      {K}];
    If[opt,
      lcelist = Rest[FoldList[Plus, 0, Re[Log[s]]]]/Range[K];
      Return[ConvergencePlot[lcelist] ],
      lces = Sort[Re[Apply[Plus, Log[s]]]/K, Greater];
      Return[{lces, LyapunovDimension[lces]}]
    ];
  ]

showOrbit[sol_, patt_, f_] :=
Module[{n, orbit, xxx, zzz},
    n = Length[First[sol]];
    Which[
      n >= 3,
        orbit = If[n == 3 && patt == {1,2,3}, sol, 
                  Map[#[[patt]]&, sol] ];
        Show[Graphics3D[f[orbit]], PlotRange -> All, Axes -> Automatic],
      n == 2,
        Show[Graphics[f[orbit]], PlotRange -> All, Frame -> True],
      n == 1,
        xxx = Map[First, sol];
        zzz = Transpose[{Drop[xxx, -1], Drop[xxx, 1]}];
        Show[Graphics[f[zzz]], PlotRange -> All, Frame -> True]
    ] ]
    
PhaseSpaceC[f_, initcond_, time_, trans_:0, 
            stepsize_:0.02, patt_:{1,2,3}] :=
Module[{n, a, xxx, xxx0, sol},
    n = Length[initcond];
    xxx = Array[a, n];
    xxx0 = RKPoint[f[xxx], xxx, initcond, {trans, stepsize}];
    sol = RKList[f[xxx], xxx, xxx0, {time, stepsize}];
    showOrbit[sol, patt, Line] ]

PhaseSpaceD[f_, initcond_, time_, trans_:0, patt_:{1,2,3}] :=
Module[{n, xxx0, sol},
    n = Length[initcond];
    xxx0 = Nest[f, N[initcond], trans];
    sol = NestList[f, xxx0, time];
    showOrbit[sol, patt, Map[Point, #]&] ]

(* Project *)
prj[v1_, v2_] := (v2.v1) v2/(v2.v2)
multiprj[v1_, vecs_] := 
    Plus @@ Map[prj[v1, #]&, vecs]
(* Gram-Schmidt Orthogonalization *)
GramSchm[vecs_] := 
    Fold[Join[#1,{#2 - multiprj[#2, #1]}]&, {}, vecs];

(* End[] *)

Protect[LCEsD, LCEsC, PlotLCEsC, ConvergencePlot, PhaseSpaceD, PhaseSpaceC, 
    LyapunovDimension, RKList, RKPoint, IntVarEq, GramSchm]

EndPackage[]
