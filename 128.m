/*
Showing that X_0(128) has no translates of E in W_7^1 over F_3
*/


// Pick a prime of good reduction
p := 3;

print "Initializing curves";

P8F<a,b,c,d,e,f,g,h,i> := ProjectiveSpace(GF(p),8);
P2F<x,y,z> := ProjectiveSpace(GF(p),2);

// equations from geteqns.m
XF := Curve(P8F, [
    a*b + g*i,
    -a*d + g*h,
    -a*e + f*i,
    a*c + f*h,
    e*h + c*i,
    b*f + e*g,
    a^2 + d*i,
    -a^2 + b*h,
    d*f + c*g,
    d*e + a*f,
    b*c + a*f,
    b*d - a*g,
    a*b - a*d + f^2 - g*h,
    e*f + b*h + b*i - d*i,
    -a^2 + c*f + 2*d*h,
    -c*f + g^2 + 2*d*h - b*i - d*i,
    c*e - 2*a*h - a*i,
    2*c^2 + d*g + 2*a*h - a*i,
    2*c^2 + e^2 - b*g + d*g - 2*a*h + a*i,
    a*g + 4*h^2 + i^2,
    f*g - 4*c*h + e*i
]);

EF := Curve(P2F, y^2*z - x^3-x^2*z-x*z^2-z^3);

phiF := map<XF -> EF | [
    g - 2*h - i,
    2*c + e,
    2*a + 2*h + i
]>;


assert Genus(XF) eq 9;
assert IsReduced(XF);
assert IsIrreducible(XF);

// Finding generator of E(F_3)
E := EllipticCurve([0, 1, 0, 1, 1]);
E := ChangeRing(E, GF(p));

assert #Points(E) eq 6;
assert Order(E![1,1,1]) eq 6;
assert IsIsomorphic(E,EF);

bool, iso := IsIsomorphic(E,EF);

P := EF![1,1,1];

assert iso(E![1,1,1]) eq P;

zero := EF![0,1,0];

print "Computing pullbacks";

Da := Pullback(phiF,Place(P));
Db := Pullback(phiF, Place(zero));
D0 := Da -Db;
// D0 is the image of a generator on E(F_3) under  E -> J_0

print "Finding all deg 7 divisors";

// Get all places of degree <= 7
place_list := [];
for d in [1..7] do
    deg_d := Places(XF,d);
    Append(~place_list, deg_d);
    print "- Added places of degree", d;
end for;

// find all ways to get a deg 7 divisor as sum of lower degree places
parts := Partitions(7);

// only consider ones that can possibly move: 
// pigeonhole principle implies that any deg 7 divisor that moves must be linearly equivalent
// to a divisor with at most #X(F_p) // p+1 deg 1 places in its support
good_parts := [];
for P in parts do
    if Multiplicity(P, 1) le (#Points(XF)) div (p+1) then
        Append(~good_parts, P);
    end if;
end for;

print "Checking which deg 7 divisors move...";

divs := [];

for part in good_parts do
    
    // for each partition of 7, 
    // consider all divisors that are sums of places of degrees equal to the parts
    deg_part := CartesianProduct([place_list[d] : d in part]);
    part;    
    total := #deg_part;
    counter:=1;

    // each element of deg_part is a tuple of places whose degrees sum to 7
    for summands in deg_part do

        // progress check
        if counter mod 100 eq 0 then
            printf "%o of %o divisors analyzed\r", counter, total;
        end if;

        // construct D as the sum of the lower degree places
        len := #summands;        
        D := 0*Divisor(summands[1]);
        for i in [1..len] do
            D := D + Divisor(summands[i]);
        end for;
    
        // check the dimension of L(D)
        dim := Dimension(D);

        // if D moves, 
        // determine if a divisor linearly equivalent to D was already added to the list
        if dim gt 1 then
            already_checked := false;
            for old_divisor in divs do
                if IsLinearlyEquivalent(D, old_divisor) then
                    already_checked := true;
                end if;
            end for;
            
            // otherwise, add D to the list
            if not already_checked then
                Append(~divs, D);
            end if;
        end if;

        counter:= counter +1;
    end for;
    print "Done";
end for;

// For each degree 7 divisor that moves, check if its translate by D0 also moves
todo := [];
for D in divs do
    dim := Dimension(RiemannRochSpace(D+D0)); // dimension of L(D+D_0)
    if dim gt 1 then // if dimension is strictly greater than 1, then the divisor moves
        Append(~todo, D);
    end if;
end for;

print "Nr. of divisors D such that D+D0 in W_7^1:", #todo;

// For the deg 7 divisors D such that D and D+D0 move, check all translates D+i*D_0
todo2 := [];
for D in todo do
    dims := [Dimension(RiemannRochSpace(D+i*D0)) : i in [1..#Points(EF)]];
    if Minimum(dims) gt 1 then
        Append(~todo2, D);
    end if;
end for;

print "Nr. of divisors D such that D+i*D0 in W_7^1 for all i:", #todo2;

assert #todo2 eq 0;