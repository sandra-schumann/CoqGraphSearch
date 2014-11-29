Hp' : reachableUsing g s d p'
n1 : u <> d
Hvp : In u p'
========================
exists v, In v p' /\ hasEdge g u v



assert (lookup g u = Some neighbors -> hasEdge g u v -> In v neighbors) by
  admit.



lookup
  (fold_right (insert foundPathLen) frontierRemaining
     (map (fun v0 : node => (v0, (Some u, S (foundPathLen (u, pu)))))
        neighbors)) v = Some (Some u, S (foundPathLen (u, pu)))

