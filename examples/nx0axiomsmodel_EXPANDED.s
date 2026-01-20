%--------------------------------------------------------
tff(semantics,logic,
    $alethic_modal ==
      [ $domains == $constant,
        $designation == $rigid,
        $terms == $local,
        $modalities == $modal_system_K ] ).

tff(child_type,type,    child: $tType ).
tff(adult_type,type,    adult: $tType ).
tff(agatha_decl,type,   agatha: adult ).
tff(charly_decl,type,   charly: child ).
tff(quiet_decl,type,    quiet: child > $o ).
tff(sleepy_decl,type,   sleepy: adult > $o ).
tff(peaceful_decl,type, peaceful: child > $o ).
tff(serves_decl,type,   serves: adult > child ).
tff(rains_decl,type,    rains: $o ).

tff(child_d_decl,type, child_d: $tType).
tff(adult_d_decl,type, adult_d: $tType).
tff(child_1_decl,type,child_1:child_d).
tff(adult_1_decl,type,adult_1:adult_d).
tff(d2child_decl,type, d2child: child_d > child).
tff(d2adult_decl,type, d2adult: adult_d > adult).

tff(w1_decl,type,w1:     $world).
tff(w2_decl,type,w2:     $world).
tff(w3_decl,type,w3:     $world).

tff(leo_workers_worlds,interpretation-worlds,
    ( ! [W: $world] : ( W = w1 | W = w2 | W = w3 )
    & $distinct(w1,w2,w3)
    & $local_world = w1
    & $accessible_world(w1,w1)
    & $accessible_world(w1,w2)
    & $accessible_world(w2,w2)
    & $accessible_world(w2,w3)
    & $accessible_world(w3,w1)
    ) ).
tff(people_ds,interpretation-domains,
    ! [W: $world] :
      $in_world(W,
        ( ! [C: child] : 
            ? [CD: child_d] : C = d2child(CD)
        & ! [CD: child_d] : CD = child_1
        & ! [CD1: child_d,CD2: child_d] :
            ( d2child(CD1) = d2child(CD2) => CD1 = CD2 )
        & ! [A: adult] : 
            ? [AD: adult_d] : A = d2adult(AD)
        & ! [AD: adult_d] : AD = adult_1
        & ! [AD1: adult_d,AD2: adult_d] :
            ( d2adult(AD1) = d2adult(AD2) 
           => AD1 = AD2 ) )) ).

tff(people_mappings,interpretation-mappings,
    ! [W: $world] :
      $in_world(W,
        ( charly = d2adult(child_1)
        & agatha = d2adult(adult_1)
        & serves(d2adult(adult_1)) = d2child(child_1)
        & ~ quiet(d2child(child_1))
        & ~ sleepy(d2adult(adult_1))
        & peaceful(d2child(child_1))
        & people_mappings(d2child(child_1))
        & rains )) ).
%--------------------------------------------------------
