let swing_tail q =
  let old_tail =
    Atomic.get q.tail
    (*@ Ghost.scope (fun step ->
      let (root, head, last, tail, retired_values, values,
           retired_fp, active_fp, retired_links, active_links,
           waiting, waiting_on) =
        unfold is_queue q {root; head; last; tail; retired_values; values;
          retired_fp; active_fp; retired_links; active_links; waiting;
          waiting_on} in
      let result = step () in
      is_queue_published_snapshot q
        (Finset.union retired_fp (Finset.union active_fp (Finset.singleton last)))
        (Finset.union retired_links active_links)
        (Finset.union retired_fp (Finset.singleton head)) waiting result;
      fold is_queue q;
      result) *)
  in
  match
    Atomic.get old_tail
    (*@ Ghost.scope (fun step ->
      let (root, head, last, tail, retired_values, values,
           retired_fp, active_fp, retired_links, active_links,
           waiting, waiting_on) =
        unfold is_queue q {root; head; last; tail; retired_values; values;
          retired_fp; active_fp; retired_links; active_links; waiting;
          waiting_on} in
      is_queue_published_observe q old_tail
        (Finset.union retired_fp (Finset.union active_fp (Finset.singleton last)))
        (Finset.union retired_links active_links)
        (Finset.union retired_fp (Finset.singleton head)) waiting;
      segment_info root head;
      segment_info head last;
      let exposure =
        if old_tail == last then At_last
        else if Finset.mem old_tail retired_fp then
          let (before, before_fp, before_links, value, next,
               after, after_fp, after_links) =
            segment_split root head retired_values retired_fp retired_links old_tail in
          Retired_cell (before, before_fp, before_links, value, next,
            after, after_fp, after_links)
        else
          let (before, before_fp, before_links, value, next,
               after, after_fp, after_links) =
            segment_split head last values active_fp active_links old_tail in
          Active_cell (before, before_fp, before_links, value, next,
            after, after_fp, after_links)
      in
      let result = step () in
      begin match exposure with
      | At_last -> ()
      | Retired_cell (before, before_fp, before_links, value, next,
          after, after_fp, after_links) ->
          segment_restore root old_tail next head before after
            before_fp after_fp before_links after_links value
      | Active_cell (before, before_fp, before_links, value, next,
          after, after_fp, after_links) ->
          segment_restore head old_tail next last before after
            before_fp after_fp before_links after_links value
      end;
      begin match result with
      | Nil -> ()
      | Next (value, next) ->
          is_queue_link_snapshot q
            (Finset.union retired_fp (Finset.union active_fp (Finset.singleton last)))
            (Finset.union retired_links active_links)
            (Finset.union retired_fp (Finset.singleton head)) waiting
            (Edge (old_tail, value, next))
      end;
      fold is_queue q;
      result) *)
  with
  | Nil -> ()
  | Next (value, next) ->
      if
        Atomic.compare_and_set q.tail old_tail next
        (*@ Ghost.scope (fun step ->
          let (root, head, last, tail, retired_values, values,
               retired_fp, active_fp, retired_links, active_links,
               waiting, waiting_on) =
            unfold is_queue q {root; head; last; tail; retired_values; values;
              retired_fp; active_fp; retired_links; active_links; waiting;
              waiting_on} in
          is_queue_link_observe q (Edge (old_tail, value, next))
            (Finset.union retired_fp (Finset.union active_fp (Finset.singleton last)))
            (Finset.union retired_links active_links)
            (Finset.union retired_fp (Finset.singleton head)) waiting;
          consecutive_segment_edges root head last retired_values values
            retired_fp active_fp retired_links active_links;
          segment_info head last;
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
