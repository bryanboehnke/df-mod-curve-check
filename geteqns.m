// follow install instructions from (https://github.com/rouseja/ModCrvToEC),
// may need to change filepath for install location
AttachSpec("/Applications/Magma/Modular-main/Modular.spec");
Attach("/Applications/Magma/ModCrvToEC.m"); 

/*
N := 82;
gens := [[7,7,0,69],[45,25,0,71],[51,4,0,71]];
ModEC := InitializeModEC(N,gens : Verbose:= true);
(https://beta.lmfdb.org/ModularCurve/Q/82.126.9.a.1/)

N := 86;
gens := [[33,82,0,59],[47,31,0,51],[67,20,0,5]];
ModEC := InitializeModEC(N,gens : Verbose:= true);
(https://beta.lmfdb.org/ModularCurve/Q/86.132.10.a.1/)

N := 92;
gens := [[7,62,0,81],[9,35,0,7],[27,14,0,45],[31,50,0,15],[63,59,0,87]];
ModEC := InitializeModEC(N,gens : Verbose:= true);
(https://beta.lmfdb.org/ModularCurve/Q/92.144.10.c.1/)

N := 99;
gens := [[41,64,0,40],[46,79,0,79],[58,69,0,68],[61,17,0,67]];
ModEC := InitializeModEC(N,gens : Verbose:= true);
(https://beta.lmfdb.org/ModularCurve/Q/99.144.9.a.1/)
-- multiple elliptic curves

N := 128;
gens := [[3,0,0,97],[67,21,0,119],[89,91,0,41],[115,23,0,11],[117,70,0,75]];
ModEC := InitializeModEC(N,gens : Verbose:= true);
(https://beta.lmfdb.org/ModularCurve/Q/128.192.9.b.1/)
-- multiple elliptic curvees
*/

SetSeed(31415,0);
// N := 82;
// gens := [[7,7,0,69],[45,25,0,71],[51,4,0,71]];
N := 92;
gens := [[7,62,0,81],[9,35,0,7],[27,14,0,45],[31,50,0,15],[63,59,0,87]];

printf "Finding defining equations for X_0(%o).\n", N;

ModEC := InitializeModEC(N,gens : Verbose:= true);

pts := PointSearch(ModEC`XG,100);
ModEC`BasePt := pts[1];
// Iso, Mults := EllipticCurveQuoCandidates(ModEC : OnlyRankZero := false); 

/* 
certain levels have maps to multiple elliptic curves (including those with rank zero)

// N = 82
Map := FindMapsToEC(ModEC, [[1, 0, 1, -2, 0]], [1]);

// N = 86
Map := FindMapsToEC(ModEC, [[0, 1, 1, 0, 0]], [2]);

// N = 92
Map := FindMapsToEC(ModEC, [[0, 0, 0, -1, 1]], [1])

// N = 99
Map := FindMapsToEC(ModEC, [[1, -1, 1, -2, 0]], [1]);

// N = 128
Map := FindMapsToEC(ModEC, [[0, 1, 0, 1, 1]], [1]);
*/

// N = 92

// Map := FindMapsToEC(ModEC, Iso, Mults);
Map := FindMapsToEC(ModEC, [[0, 0, 0, -1, 1]], [1])

X := Domain(Map[1]);
E := Codomain(Map[1]);
phi := Map[1];

// P8<a,b,c,d,e,f,g,h,i> := AmbientSpace(X);
P9<a,b,c,d,e,f,g,h,i,j> := AmbientSpace(X);
P2<x,y,z> := AmbientSpace(E);

printf "Defining equations for X_0(%o): \n", N;
DefiningEquations(X);

printf "Defining equations for positive-rank elliptic curve E of conductor %o: \n", N;
DefiningEquations(E);

printf "Defining equations for modular parameterization phi: X_0(%o) -> E: \n", N;
DefiningEquations(phi);