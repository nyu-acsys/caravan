let swing_tail q =
  let old_tail =
    Atomic.get q.tail
    (*@ Ghost.scope (fun step ->
      let s = unfold is_queue q in
      let result = step () in
      issue_fact q s (Published result);
      fold is_queue q;
      result) *)
  in
  match
    Atomic.get old_tail
    (*@ Ghost.scope (fun step ->
      let s = unfold is_queue q in
      observe_fact q s (Published old_tail);
      segment_info s.root s.head;
      segment_info s.head s.last;
      let exposure =
        if old_tail == s.last then At_last
        else if Finset.mem old_tail s.retired_fp then
          let (before, before_fp, before_links, value, next,
               after, after_fp, after_links) =
            segment_split s.root s.head s.retired_values s.retired_fp s.retired_links old_tail in
          Retired_cell (before, before_fp, before_links, value, next,
            after, after_fp, after_links)
        else
          let (before, before_fp, before_links, value, next,
               after, after_fp, after_links) =
            segment_split s.head s.last s.values s.active_fp s.active_links old_tail in
          Active_cell (before, before_fp, before_links, value, next,
            after, after_fp, after_links)
      in
      let result = step () in
      begin match exposure with
      | At_last -> ()
      | Retired_cell (before, before_fp, before_links, value, next,
          after, after_fp, after_links) ->
          segment_restore s.root old_tail next s.head before after
            before_fp after_fp before_links after_links value
      | Active_cell (before, before_fp, before_links, value, next,
          after, after_fp, after_links) ->
          segment_restore s.head old_tail next s.last before after
            before_fp after_fp before_links after_links value
      end;
      begin match result with
      | Nil -> ()
      | Next (value, next) ->
          issue_fact q s (Linked (Edge (old_tail, value, next)))
      end;
      fold is_queue q;
      result) *)
  with
  | Nil -> ()
  | Next (value, next) ->
      if
        Atomic.compare_and_set q.tail old_tail next
        (*@ Ghost.scope (fun step ->
          let s = unfold is_queue q in
          observe_fact q s (Linked (Edge (old_tail, value, next)));
          consecutive_segment_edges s.root s.head s.last s.retired_values s.values
            s.retired_fp s.active_fp s.retired_links s.active_links;
          segment_info s.head s.last;
          let result = step () in
          if result then
            fold is_queue q {tail = next}
          else
            fold is_queue q;
          result) *)
      then ()
      else ()
(*@ manual *)
(*@ swing_tail q requires is_queue q *)
