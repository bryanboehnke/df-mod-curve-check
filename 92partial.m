/*
Showing that X_0(92) has no translates of E in W_8^1 over F_5
(genus 10, mult 1)
*/

SetSeed(31415,0)

// Pick a prime of good reduction
p := 3;

print "Initializing curves.";

P9F<a,b,c,d,e,f,g,h,i,j> := ProjectiveSpace(GF(p),9);
P2F<x,y,z> := ProjectiveSpace(GF(p),2);

// equations from geteqns.m
XF := Curve(P9F, [
    a*b - a*d + f^2 - a*g - g*i,
    -a*c - a*d + f^2 + e*g,
    a*e + a*f - a*g - e*g + a*j - g*j,
    -a*d - b*d - b*e + f*i + a*j - f*j,
    b*c + f^2 + f*g + f*j - g*j,
    a*c + a*d + e*f + a*g - a*j + f*j,
    -a*b - a*e - b*e + e*f + a*g - f*g - f*j + g*j,
    -a*c - b*d + d^2 - b*e - b*f + f^2 - g*i + f*j - i*j,
    a^2 + a*d + a*e - a*f - b*f - e*f + a*i,
    -a^2 + a*c + b*e + a*f - e*g + g^2 + g*i + f*j - g*j,
    -a*c + d^2 + a*f - b*f - e*f + a*j + e*j,
    a*c + a*e + a*f + a*i + e*i + f*i - f*j + i*j,
    a^2 - a*c + a*e + e^2 + a*j + e*j,
    -b*d - b*e - a*f + a*g + d*j - i*j,
    a*d - a*f - f^2 + d*g,
    -a*b - a*c + a*f + d*f + e*f,
    a*d + d^2 + d*e - b*f - e*f,
    a^2 + a*d + a*e + f*g + c*j + f*j,
    -b*c + e*g + c*i - a*j + g*j,
    a^2 + a*d + a*e + c*g + f*j - g*j,
    -b*c + a*d + a*e + c*f - f^2,
    a*c + b*c - a*e + c*e + a*g,
    -b*c + c*d + a*e,
    b*c + c^2 + f*g,
    -a^2 - f^2 + b*g,
    -a*d + f^2 - f*g + a*i + b*j - 2*f*j,
    -b^2 - a*c - b*c + b*f - f^2 + d*i - f*i + f*j - i*j,
    -a^2 - b*f - e*f - b*g - 2*c*h - d*h + 2*f*h - 2*g*h + h^2 - d*i + e*i - h*i
        + b*j + c*j + f*j - g*j + 4*h*j - i*j

]);

EF := Curve(P2F, -x^3 + y^2*z + x*z^2 - z^3);

phiF := map<XF -> EF | [
    b + f + g,
    -2*c - d + 2*f - 2*g + 2*h - i + 4*j,
    f - g
]>;

//
assert Genus(XF) eq 10;
assert IsReduced(XF);
assert IsIrreducible(XF);

// Finding generator of E(F_p)
E := EllipticCurve([0, 0, 0, -1, 1]);
E := ChangeRing(E, GF(p));

assert #Points(E) eq 7;
assert Order(E![1,1,1]) eq 7;
assert IsIsomorphic(E,EF);

bool, iso := IsIsomorphic(E,EF);

P := EF![1,1,1];

assert iso(E![1,1,1]) eq P;

print "Computing pullbacks.";

zero := EF![0,1,0];

Da := Pullback(phiF,Place(P));
Db := Pullback(phiF, Place(zero));
D0 := Da -Db;

print "Finding all deg 8 divisors.";

// Get all places of degree <= 8
place_list := [];
for d in [1..8] do
    deg_d := Places(XF,d);
    Append(~place_list, deg_d);
    print "- Added places of degree", d;
end for;

// find all ways to get a deg 8 divisor as sum of lower degree places
parts := Partitions(8);

// only consider ones that can possibly move: 
// pigeonhole principle implies that any deg 7 divisor that moves must be linearly equivalent
// to a divisor with at most #X(F_p) // p+1 deg 1 places in its support
// good_parts := [];
// for P in parts do
//     if Multiplicity(P, 1) le (#Points(XF)) div (p+1) then
//         Append(~good_parts, P);
//     end if;
// end for;

good_parts := [
    [ 8 ],
    [ 7, 1 ],
    [ 6, 2 ],
    [ 5, 3 ],
    [ 5, 2, 1 ],
    [ 4, 4 ],
    [ 4, 3, 1 ],
    [ 4, 2, 2 ],
    [ 3, 3, 2 ],
    [ 3, 2, 2, 1 ]];


print "Checking which deg 8 divisors move.";

divs := [];

for part in good_parts do

    // for each partition of 8, 
    // consider all divisors that are sums of places of degrees equal to the parts
    deg_part := CartesianProduct([place_list[d] : d in part]);
    part;    
    total := #deg_part;
    counter:=1;

    // each element of deg_part is a tuple of places whose degrees sum to 8
    for summands in deg_part do

        // progress check
        if counter mod 100 eq 0 then
            printf "%o of %o divisors of type %o analyzed\r", counter, total, part;
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

// For each degree 8 divisor that moves, check if its translate by D0 also moves
todo := [];
for D in divs do
    dim := Dimension(RiemannRochSpace(D+D0));
    if dim gt 1 then
        Append(~todo, D);
    end if;
end for;

print "\nNr. of divisors D such that D+D0 in W_8^1:", #todo;

todo2 := [];
for D in todo do
    dims := [Dimension(RiemannRochSpace(D+i*D0)) : i in [1..#Points(EF)]];
    //print dims;
    if Minimum(dims) gt 1 then
        Append(~todo2, D);
    end if;
end for;

print "Nr. of divisors D such that D+iD0 in W_8^1 for all i:", #todo2;

assert #todo2 eq 0;
