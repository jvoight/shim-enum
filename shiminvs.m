//////////////////////////////////////////////////////////////////////////////
//
// Invariants of Arithmetic Fuchsian groups
// November 2007, John Voight
//
//////////////////////////////////////////////////////////////////////////////

//-------------
//
// Enumerative functions: List (prime, almost prime) ideals of bounded norm.
//
//-------------

PrimeIdealsWithAdjPsiLe := function(Z_F, D, B);
  P := [];
  NP := [];
  BB := 2*B-1;

  // Such an ideal aa is composed of primes pp with Psi(pp) = N(pp) <= 2*B-1.
  for p in PrimesUpTo(Floor(BB)) do
    pFacts := Decomposition(Z_F, p);
    Pnew := [pp[1] : pp in pFacts | Norm(pp[1]) le BB and pp[1] + D eq ideal<Z_F | 1>];
    P cat:= Pnew;
    NP cat:= [Norm(pp) : pp in Pnew];
  end for;
  return P, NP;
end function;

IdealsWithAdjPsiLe := function(Z_F, D, B);
  // This function returns all ideals N of Z_F prime to D with Psi'(N) <= B.
  // Psi is the multiplicative function which on prime power ideals is defined by 
  //   Psi'(pp^e) = N(pp)^(e-1)*(N(pp)+1)/2.

  P := [];
  NP := [];
  BB := 2*B-1;

  // Such an ideal aa is composed of primes pp with Psi(pp) = N(pp) <= 2*B-1.
  for p in PrimesUpTo(Floor(BB)) do
    pFacts := Decomposition(Z_F, p);
    Pnew := [pp[1] : pp in pFacts | Norm(pp[1]) le BB and pp[1] + D eq ideal<Z_F | 1>];
    P cat:= Pnew;
    NP cat:= [Norm(pp) : pp in Pnew];
  end for;

  // Internal function which takes the list of primes and recursively
  // adds products which fall within the bounds.
  IdealsWithAdjPsiLeInternal := function(Z_F, B, P, NP);
    if #P eq 0 then
      return [ideal<Z_F | 1>], [1];
    end if;
    Pout := [];
    NPout := [];
    pp := P[1];
    Npp := NP[1];
    ebnd := Ceiling(Log(Npp, 2*B/(Npp+1)))+1;
    for e := ebnd to 0 by -1 do
      // Recurse on the first ideal: for each power which lies within the
      // bounds, list all future ideals with Psi newly bounded.
      if e eq 0 then
        ppe := ideal<Z_F | 1>;
        Nphippe := 1;
      else
        ppe := pp^e;
        Nphippe := Npp^(e-1)*(Npp+1)/2;
      end if;
      qqs, Nqqs := ($$)(Z_F, B/Nphippe, P[2..#P], NP[2..#P]);
      if #qqs gt 0 then
        Pout cat:= [ppe*qq : qq in qqs];
        NPout cat:= [Nphippe*Nqq : Nqq in Nqqs];
      end if;
    end for;
    return Pout, NPout;
  end function;

  P, NP := IdealsWithAdjPsiLeInternal(Z_F, B, P, NP);

  // Sort ideals by value of Psi.
  permut := [];
  Sort(~NP, ~permut);
  permut := Eltseq(permut);
  P := [P[permut[i]] : i in [1..#permut]];
  // Remove trivial ideal.
  i := 1;
  while P[i] ne ideal<Z_F | 1> do
    i +:= 1;
  end while;
  P := P[1..i-1] cat P[i+1..#P];

  return P, NP;
end function;

IdealsWithPsiLe := function(Z_F, B, P, NP);
  BB := B-1;

  // Internal function which takes the list of primes and recursively
  // adds products which fall within the bounds.
  IdealsWithAdjPsiLeInternal := function(Z_F, B, P, NP);
    if #P eq 0 then
      return [ideal<Z_F | 1>], [1];
    end if;
    Pout := [];
    NPout := [];
    pp := P[1];
    Npp := NP[1];
    ebnd := Floor(Log(Npp, B/(Npp+1)))+1;
    for e := ebnd to 0 by -1 do
      // Recurse on the first ideal: for each power which lies within the
      // bounds, list all future ideals with Psi newly bounded.
      if e eq 0 then
        ppe := ideal<Z_F | 1>;
        Nphippe := 1;
      else
        ppe := pp^e;
        Nphippe := Npp^(e-1)*(Npp+1);
      end if;
      qqs, Nqqs := ($$)(Z_F, B/Nphippe, P[2..#P], NP[2..#P]);
      if #qqs gt 0 then
        Pout cat:= [ppe*qq : qq in qqs];
        NPout cat:= [Nphippe*Nqq : Nqq in Nqqs];
      end if;
    end for;
    return Pout, NPout;
  end function;

  P, NP := IdealsWithAdjPsiLeInternal(Z_F, B, P, NP);

  // Sort ideals by value of Psi.
  permut := [];
  Sort(~NP, ~permut);
  permut := Eltseq(permut);
  P := [P[permut[i]] : i in [1..#permut]];
  // Remove trivial ideal.
  i := 1;
  while P[i] ne ideal<Z_F | 1> do
    i +:= 1;
  end while;
  P := P[1..i-1] cat P[i+1..#P];

  return P, NP;
end function;

PrimeIdealsWithAdjPhiLe := function(Z_F, B);
  // This function returns all prime ideal pp of Z_F with Phi'(pp) <= B.
  // Phi' is the generalized Euler phi-function which on prime power ideals is 
  // defined by 
  //   Phi'(pp^e) = N(pp)^(e-1)*(N(pp)-1)/2.

  P := [];
  NP := [];
  BB := 2*B+1;
  for p in PrimesUpTo(Floor(BB)) do
    pFacts := Decomposition(Z_F, p);
    Pnew := [pp[1] : pp in pFacts | Norm(pp[1]) le BB];
    P cat:= Pnew;
    NP cat:= [(Norm(pp)-1)/2 : pp in Pnew];
  end for;

  if #P eq 0 then
    return [], [];
  end if;

  // Sort.
  permut := [];
  Sort(~NP, ~permut);
  permut := Eltseq(permut);
  P := [P[permut[i]] : i in [1..#permut]];
  return P, NP;
end function;

TwoPrimeIdealsWithAdjPhiLe := function(Z_F, B);
  // This function returns all products of two distinct prime ideals pp*qq of Z_F 
  // with Phi'(pp*qq) <= B.

  // List all prime ideals within the bounds, and for each such prime, list the 
  // possibilities for the second with the new bound.
  P, NP := PrimeIdealsWithAdjPhiLe(Z_F, B);
  PP := [];
  NPP := [];
  for i := 1 to #P do
    j := 1;
    Bp := B/NP[i];
    while j le #NP and NP[j] le Bp do
      j +:= 1;
    end while;
    if j gt 1 and NP[j-1] le Bp then
      PP cat:= [P[i]*P[k] : k in [1..j-1] | i ne k];
      NPP cat:= [NP[i]*NP[k] : k in [1..j-1] | i ne k];
    end if;
  end for;

  if #PP eq 0 then
    return [], [];
  end if;

  PP := SetToSequence(SequenceToSet(PP));
  NPP := [Norm(PP[i]) : i in [1..#PP]];

  // Sort.
  if #PP gt 0 then
    permut := [];
    Sort(~NPP, ~permut);
    permut := Eltseq(permut);
    PP := [PP[permut[i]] : i in [1..#permut]];
  end if;
  
  return PP, NPP;
end function;

EvenFactorIdealsWithAdjPhiLe := function(Z_F, B);
  // This function returns all products aa of distinct prime ideals of Z_F
  // with Phi'(aa) <= B.

  PP, NPP := TwoPrimeIdealsWithAdjPhiLe(Z_F, B);
  if #PP eq 0 then
    return [], [];
  end if;
  repeat
    changed := false;
    for i := 1 to #PP do
      j := i+1;
      while j le #NPP and NPP[i]*NPP[j] le B do
        if PP[i] + PP[j] eq ideal<Z_F | 1> and PP[i]*PP[j] notin PP then
          Append(~PP, PP[i]*PP[j]);
          Append(~NPP, NPP[i]*NPP[j]);
          changed := true;
        end if;
        j +:= 1;
      end while;
    end for;
    if changed then
      permut := [];
      Sort(~NPP, ~permut);
      permut := Eltseq(permut);
      PP := [PP[permut[i]] : i in [1..#permut]];
    end if;
    print NPP;
  until not changed;

  return PP[2..#PP], NPP[2..#NPP];
end function;

//-------------
//
// Main function
//
//-------------

intrinsic FuchsianGroups(F::FldNum, g::RngIntElt : LF := []) -> SeqEnum
  {Returns the Shimura curves of genus <=g over F.}

  // Find all cyclotomic quadratic extensions.
  S := CyclotomicQuadraticExtensions(F);
  // S := S[1..#S]; // Remove trivial extension
  // Sort out from prime powers all possible m such that [F(zeta_m):F] = 2.
  Sdiv := Divisors(&*S[2..#S]);
  e2 := Valuation(S[1], 2);
  Sdiv := [2^i*s : i in [0] cat [2..e2], s in Sdiv];
  Sdiv := Sdiv[2..#Sdiv];
  Sdiv := [m : m in Sdiv |
           &and[Degree(f[1]) eq 2 : f in Factorization(CyclotomicPolynomial(m), F)]];

  print "Cyclotomic quadratic extensions:", Sdiv;

  // Primitive part of the area: the area is Aprim*Phi(d)*Psi(N).
  Z_F := MaximalOrder(F);
  d := Degree(F);
  Lden := Lcm(Sdiv);
  if LF cmpeq [] then
    z := Re(Evaluate(LSeries(NumberField(F)), -1));
    tz10 := Log(Lden*Abs(z))/Log(10);
    if tz10 ge 4 then
      z := RealField()!Evaluate(LSeries(NumberField(F) : Precision := Ceiling(tz10)+3), -1);
    end if;
    z := Round(Lden*z)/Lden;
    Aprim := (-1)^d/2^(d-2)*z;
  else
    Aprim := (-1)^d/2^(d-2)*LF;
  end if;

  print "Aprim:", Aprim;

  if Abs(Aprim) gt 64/3*(g+1) then
    print "Aprim > Selberg-Zograf";
    return [];
  end if;

  resultGroups := [];

  if Degree(F) mod 2 eq 1 then
    G := FuchsianGroup(F, ideal<Z_F | 1>, ideal<Z_F | 1> : TotallyPositive := false, ComputeAlgebra := false);
    sig := EllipticInvariants(G);
    g0 := Genus(G);
    if g0 le g then
      Append(~resultGroups, <ideal<Z_F | 1>, Signature(G)>);
    end if;
    calD := TwoPrimeIdealsWithAdjPhiLe(Z_F, 1+2*(g-g0)/Aprim);  
  else
    calD := PrimeIdealsWithAdjPhiLe(Z_F, 2/Aprim*64/3*(g+1));
    if #PrimeIdealsWithAdjPhiLe(Z_F, 2/Aprim*64/3*(g+1)) eq 0 and d mod 2 eq 0 then
      print "No ideals with Phi(pp) <= ", 2/Aprim*64/3*(g+1);
      return [];
    end if;
    G := FuchsianGroup(F, Factorization(2*Z_F)[1][1], ideal<Z_F | 1> : TotallyPositive := false, ComputeAlgebra := false);
    sig := EllipticInvariants(G : CoerceIntegers := false);
  end if;

  _ := CyclotomicClassNumbers(F);
  print "calD:", [Norm(D) : D in calD];
  Z_Ks := [];
  for q in Sdiv do
    for i := 1 to #F`CyclotomicClassNumbers[1] do
      if q mod F`CyclotomicClassNumbers[1][i] eq 0 then
        Append(~Z_Ks, F`CyclotomicClassNumbers[3][i]);
        break i;
      end if;
    end for;
  end for;

  for D in calD do
    print "...trying DD:", Norm(D);
    G := FuchsianGroup(F, D, ideal<Z_F | 1> : TotallyPositive := false, ComputeAlgebra := false);
    G`ShimVolume := Aprim* &*[ Norm(P[1])-1 : P in Factorization(D)];
    g0 := Genus(G);
    if g0 le g then
      Append(~resultGroups, <D, Signature(G)>);
    end if;
    A := Aprim * &*[Norm(pp[1])-1 : pp in Factorization(D)];
    DDs := EvenFactorIdealsWithAdjPhiLe(Z_F, 1+2*(g-g0)/A);
    for DD in [DD : DD in DDs | DD + D eq ideal<Z_F | 1>] do
      print "  ...trying DD*D:", Norm(DD*D);
      G := FuchsianGroup(F, DD*D, ideal<Z_F | 1> : TotallyPositive := false, ComputeAlgebra := false);
      if Genus(G) le g then
        Append(~resultGroups, <DD*D, Signature(G)>);
      end if;
    end for;
  end for;

/*
    // Throw in all primes dividing the cyclotomic quadratic powers;
    // we may then look using the primitive elliptic invariants.
    Ds := [pp[1] : pp in Factorization(ideal<Z_F | &*Sdiv>) | 
                   Norm(pp[1]) le 64/3*(g+1)/Aprim+1];
    sigs := [ [] : i in [1..#Ds]];

    // For pp (split or ramified at K), loop.
    for f in CartesianPower([0,2],#Sdiv) do
      // The factor t = Phi(d)*Psi(N) is then explicitly determined.
      sigmob := [<sig[i][1], f[i]*sig[i][2]> : i in [1..#sig]];

      print "Testing", f, "with signature", sigmob;

      for g0 := 0 to g do
        t := 1/Aprim*(2*g0-2+&+[sigmob[i][2]*(1-1/sigmob[i][1]) : i in [1..#sig]]);
    
        print "t:", t;

        // The value of t must be >0 and an integer!
        if t gt 0 and IsIntegral(t) then
          t := Integers()!t;
          // We are only searching for primes, so t = Phi(pp) = N(pp)-1.
          if t mod 2 eq 0 then
            bl, p, e := IsPrimePower(Integers()!t+1);
            if bl then
              // For this value, we must also have pp satisfying the
              // split/inert constraints posed by f.
              for pp in Decomposition(Z_F, p) do
                kappa := Norm(pp[1]);
                print kappa, Sdiv, f;
                if kappa eq p^e and 
                   &and[(kappa mod Sdiv[i] eq 1 and f[i] eq 0) or
                        (kappa mod Sdiv[i] ne 1 and f[i] eq 2) : i in [1..#f]] then
                  Append(~Ds, pp[1]);
                  Append(~sigs, sigmob);
                  print "Found prime ideal of norm", kappa;
                end if;
              end for;
            end if;
          end if;
        end if;
      end for;
    end for;

    print "Ds:", [Norm(D) : D in Ds];

    for i := 1 to #Ds do
      D := Ds[i];
      print "Trying D:", Norm(D);
      G := FuchsianGroup(F, D, ideal<Z_F | 1> : ComputeAlgebra := false);
      if D + ideal<Z_F | &*Sdiv> eq ideal<Z_F | 1> then
        G`ShimVolume := Aprim*(Norm(D)-1);
        G`ShimEllipticInvariants := sigs[i];
      end if;
      print "...has genus", Genus(G);
      if Genus(G) le g then
        Append(~resultGroups, <D, Signature(G)>);
        print "...Ds with bound", 1+2*(g-Genus(G))/(Aprim*(Norm(D)-1));
        DDs := EvenFactorIdealsWithAdjPhiLe(Z_F, 1+2*(g-Genus(G))/(Aprim*(Norm(D)-1)));
        for DD in DDs do
          if DD + D eq ideal<Z_F | 1> then
            print "...adding DD:", Norm(DD);
            G := FuchsianGroup(F, D*DD, ideal<Z_F | 1> : ComputeAlgebra := false);
            if Genus(G) le g then
              Append(~resultGroups, <D*DD, Signature(G)>);
            end if;
          end if;
        end for;
      end if;
    end for;
  end if;
*/

  print "Ds:", [Norm(D[1]): D in resultGroups];

  // Sort
  if #resultGroups gt 0 then
    permut := [];
    grpN := [Norm(D[1]) : D in resultGroups];
    Sort(~grpN, ~permut);
    permut := Eltseq(permut);
    resultGroups := [resultGroups[permut[i]] : i in [1..#permut]];

    // Level structure
    finalResultGroups := [];
    for DG in resultGroups do
      print "(Level structure) D:", Norm(DG[1]);
      R := [<DG[1], ideal<Z_F | 1>, DG[2]>];
      if Norm(DG[1]) eq 1 then
        bndDG := 1;
      else
        bndDG := &* [Norm(pp[1])-1 : pp in Factorization(DG[1])];
      end if;
      NNprimes := PrimeIdealsWithAdjPsiLe(Z_F, DG[1], 
                1+2*(g-DG[2][1])/(Aprim*bndDG));
      NNs := [];
      for NN in NNprimes do
        print "...adding NN:", NN;
        G := FuchsianGroup(F, DG[1], NN : TotallyPositive := false, ComputeAlgebra := false);
        if Genus(G) le g then
          Append(~R, <DG[1], NN, Signature(G)>);
        end if;
        if Genus(G) lt g or (Genus(G) eq g and g lt 2) then
          Append(~NNs, NN);
        end if;
      end for;
      print [Norm(NN) : NN in NNs];

      NN0s := IdealsWithPsiLe(Z_F, 64/3/(Aprim*bndDG)*(g+1), 
                              NNs, [Norm(NN) : NN in NNs]);
      NN0s := [NN0 : NN0 in NN0s | not IsPrime(NN0)];
      NNtoobig := [];
      for NN in NN0s do
//        print "...trying NN:", Norm(NN), [Norm(NN0) : NN0 in NNtoobig];
        if not &or[NN + NN0 eq NN0 : NN0 in NNtoobig] then
          print "...adding NN:", NN;
          G := FuchsianGroup(F, DG[1], NN : TotallyPositive := false, ComputeAlgebra := false);
          if Genus(G) le g then
            Append(~R, <DG[1], NN, Signature(G)>);
          end if;
          if Genus(G) gt g or (Genus(G) eq g and g ge 2) then
            Append(~NNtoobig, NN);
          end if;
        end if;
      end for;

      Append(~finalResultGroups, R);
    end for;
/*
    for DG in resultGroups do
      R := [<DG[1], ideal<Z_F | 1>, DG[2]>];
      if Norm(DG[1]) eq 1 then
        bndDG := 1;
      else
        bndDG := &* [Norm(pp[1])-1 : pp in Factorization(DG[1])];
      end if;
      NNs := IdealsWithAdjPsiLe(Z_F, DG[1], 
            1+2*(g-DG[2][1])/(Aprim*bndDG));
      print "(Level structure) D:", Norm(DG[1]);
      NNtoobig := [];
      for NN in NNs do
        if &and[NN + NN0 eq NN : NN0 in NNtoobig] then
          print "...adding NN:", Norm(NN);
          G := FuchsianGroup(F, DG[1], NN : ComputeAlgebra := false);
          if Genus(G) le g then
            Append(~R, <DG[1], NN, Signature(G)>);
          end if;
          if Genus(G) ge g then
            Append(~NNtoobig, NN);
          end if;
        end if;
      end for;
      Append(~finalResultGroups, R);
    end for;
*/
    return &cat(finalResultGroups);
  else
    return [];
  end if;
end intrinsic;

/*
Attach("shiminvs.m");
Sall := [];
for D in [D : D in [733..900] | IsFundamentalDiscriminant(D)] do
  print "===============================================================";
  print "F has discriminant", D;
  S := FuchsianGroups(QuadraticField(D),2);
  print [<Norm(v[1]), Norm(v[2]), v[3]> : v in S];
  Sall cat:= [<D, Norm(v[1]), Norm(v[2]), v[3]> : v in S];
end for;
*/

/*
Attach("shiminvs.m");
Sall := [];
for vt in T do
  print "===============================================================";
  print "F has discriminant", vt[1];
  S := FuchsianGroups(NumberField(vt[2]),2);
  print [<Norm(v[1]), Norm(v[2]), v[3]> : v in S];
  Sall cat:= [<vt[1], Norm(v[1]), Norm(v[2]), v[3]> : v in S];
end for;  
*/

/*
Attach("shiminvs.m");
F := NumberField(Polynomial([-5,0,1]));
Z_F := MaximalOrder(F);
for M in [M : M in [1..100] | M mod 2 eq 1] do
  N := ideal<Z_F | 1>;
  for p in PrimeDivisors(M) do
    pp := Decomposition(Z_F,p)[1][1];
    t := Valuation(M,p)/Valuation(Norm(pp),p);
    if IsIntegral(t) then
      N *:= Decomposition(Z_F,p)[1][1]^(Integers()!t);
    end if;
  end for;
  if Norm(N) eq M then
    G := FuchsianGroup(F, ideal<Z_F | 2>, N : ComputeAlgebra := false);
    print Norm(N), Genus(G);
  end if;
end for;
*/

/*
  iD := 1;
  while iD le #Ds do
    D := Ds[iD];
    G := FuchsianGroup(F, D, ideal<Z_F | 1>);
    if Genus(G) eq 0 then
      Append(~resultGroups, <D, ideal<Z_F | 1>, Signature(G)>);
      Ns := IdealsWithPsiLeq(Z_F, B/Norm(D), false);
      Ns := [N : N in Ns | (N + D) eq ideal<Z_F | 1>];
      iN := 2;
      while iN le #Ns do
        N := Ns[iN];
        G := FuchsianGroup(F, D, N);
        if Genus(G) eq 0 then
          Append(~resultGroups, <D, N, Signature(G)>);
        else
          jN := iN+1;
          while jN le #Ns do
            if (Ns[jN] + N) eq N then
              Remove(~Ns, jN);
            else
              jN +:= 1;
            end if;
          end while;
        end if;
        iN +:= 1;
      end while;
    end if;
    iD +:= 1;
  end while;
  return resultGroups;
*/

