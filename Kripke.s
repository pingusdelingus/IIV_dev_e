tff(semantics,logic,
    $alethic_modal ==
      [ $domains == $constant,
        $designation == $rigid,
        $terms == $local,
        $modalities == $modal_system_M ] ).

tff(child_type,type,    child: $tType ).
tff(adult_type,type,    adult: $tType ).
tff(agatha_decl,type,   agatha: adult ).
tff(charly_decl,type,   charly: child ).
tff(quiet_decl,type,    quiet: child > $o ).
tff(sleepy_decl,type,   sleepy: adult > $o ).
tff(peaceful_decl,type, peaceful: child > $o ).
tff(serves_decl,type,   serves: adult > child ).
tff(rains_decl,type,    rains: $o ).

tff(child_domain_decl,type, child_domain: $tType).
tff(adult_domain_decl,type, adult_domain: $tType).
tff(child_1_decl,type,child_1:child_domain).
tff(adult_1_decl,type,adult_1:adult_domain).
tff(domain2child_decl,type, domain2child: child_domain > child).
tff(domain2adult_decl,type, domain2adult: adult_domain > adult).

tff(w1_decl,type,w1:     $world).
tff(w2_decl,type,w2:     $world).
tff(w3_decl,type,w3:     $world).

tff(leo_workers_worlds,interpretation-worlds,
    ( ! [W: $world] : ( W = w1 | W = w2 | W = w3 )
    & $distinct(w1,w2,w3)
    & $local_world = w1
    & $accessible_world(w1,w1)
    & $accessible_world(w2,w2)
    & $accessible_world(w3,w3)
    & $accessible_world(w1,w2)
    & $accessible_world(w1,w3)
    & $accessible_world(w2,w3) ) ). 

tff(people_domains,interpretation-domains,
    ! [W: $world] :
      $in_world(W,
        ( ! [C: child] : ? [CD: child_domain] : ( C = domain2child(CD) )
        & ! [CD: child_domain] : ( CD = child_1 )
        & ! [CD1: child_domain,CD2: child_domain] :
            ( ( domain2child(CD1) = domain2child(CD2) ) => ( CD1 = CD2 ) )
        & ! [A: adult] : ? [AD: adult_domain] : ( A = domain2adult(AD) )
        & ! [AD: adult_domain] : ( AD = adult_1 )
        & ! [AD1: adult_domain,AD2: adult_domain] :
            ( ( domain2adult(AD1) = domain2adult(AD2) ) => ( AD1 = AD2 ) ) )) ).

tff(people_mappings,interpretation-mappings,
    ! [W: $world] :
      $in_world(W,
        ( ( charly = domain2adult(child_1) )
        & ( agatha = domain2adult(adult_1) )
        & ( serves(domain2adult(adult_1)) = domain2child(child_1) )
        & ~ quiet(domain2child(child_1))
        & ~ sleepy(domain2adult(adult_1))
        & peaceful(domain2child(child_1))
        & people_mappings(domain2child(child_1))
        & rains )) ).
%--------------------------------------------------------------------------------------------------
