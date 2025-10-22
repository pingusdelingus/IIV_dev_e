%------------------------------------------------------------------------------
tff(semantics,logic,
    $alethic_modal ==
      [ $domains == $constant,
        $designation == $rigid,
        $terms == $local,
        $modalities == $modal_system_M ] ).
        
tff(fruit_type,type,fruit: $tType).
tff(apple_decl,type,apple: fruit).
tff(banana_decl,type,banana: fruit).
tff(healthy_decl,type,healthy: fruit > $o).
tff(rotten_decl,type,rotten: fruit > $o).

tff(world_1_decl,type,world_1: $world).
tff(world_2_decl,type,world_2: $world).
tff(d_fruit_type,type,d_fruit: $tType).
tff(d2fruit_decl,type, d2fruit: d_fruit > fruit ).
tff(d_apple_decl,type,d_apple: d_fruit).
tff(d_banana_decl,type,d_banana: d_fruit).

tff(fruity_worlds,interpretation-worlds,
    ( ! [W: $world] : ( W = world_1 | W = world_2 )
    & $local_world = world_1
    & $accessible_world(world_1,world_1)     %----Logic is M
    & $accessible_world(world_2,world_2)
    & $accessible_world(world_1,world_2) ) ).

tff(fruity_domains,interpretation-domains,
    ! [W: $world] :
      $in_world(W,
        ( ! [F: fruit] : ? [DF: d_fruit] : F = d2fruit(DF)
        & ! [DF: d_fruit] : ( DF = d_apple | DF = d_banana )
        & $distinct(d_apple,d_banana)
        & ? [DP: d_fruit] : ( DP = d_apple )
        & ? [DP: d_fruit] : ( DP = d_banana )
        & ! [DF1: d_fruit,DF2: d_fruit] :
            ( d2fruit(DF1) = d2fruit(DF2) => DF1 = DF2 ) )) ).

tff(fruity_healthy_mappings,interpretation-mappings,
    ! [W: $world] :
      $in_world(W,
        ( apple = d2fruit(d_apple)
        & banana = d2fruit(d_banana)
        & healthy(d2fruit(d_apple))
        & healthy(d2fruit(d_banana)) )) ).

tff(fruity_rotten_mappings,interpretation-mappings,
    ( $in_world(world_1,
        ( ~ rotten(d2fruit(d_apple))
        & rotten(d2fruit(d_banana)) ))
    & $in_world(world_2,
        ( ~ rotten(d2fruit(d_apple))
        & ~ rotten(d2fruit(d_banana)) )) ) ).
%------------------------------------------------------------------------------
