(** Michael-Scott queue with an explicit segment proof. *)
type node = Nil | Next of int * node Atomic.t

type t = { head : node Atomic.t Atomic.t; tail : node Atomic.t Atomic.t }

let create () =
  let next = Atomic.make Nil in
  let head =
    Atomic.make_contended next
    (*@ initializes [Ghost.init view_queue []; Ghost.init facts_auth
      (Fact_auth.full (Facts.set Set.empty))] *)
  in
  let tail = Atomic.make_contended next in
  { head; tail }
(*@ proof
  fold queue q [];
  fold segment next next [] Finset.empty Finset.empty;
  fold segment next next [] Finset.empty Finset.empty;
  Ghost.fpu (Ghost.at facts_auth head)
    (Fact_auth.full (Facts.set Set.empty))
    (Fact_auth.full (Facts.set
      (facts_of (Finset.singleton next) Finset.empty (Finset.singleton next) Finset.empty)));
  fold is_queue q {root = next; head = next; last = next; tail = next;
    retired_values = []; values = []; retired_fp = Finset.empty; active_fp = Finset.empty;
    retired_links = Finset.empty; active_links = Finset.empty; waiting = Finset.empty;
    waiting_on = (Map.const next : (Ghost.t, node Atomic.t) map)}
*)
(*@ manual *)

let rec fix_tail tail new_tail =
  let old_tail =
    Atomic.get tail
    (*@ Ghost.scope (fun step ->
    unfold is_queue q;
    let result = step () in
    fold is_queue q;
    result) *)
  in
  if
    Atomic.get new_tail
    (*@ Ghost.scope (fun step ->
    let (root, head, last, cursor, retired_values, values, retired_fp, active_fp,
      retired_links, active_links, waiting, waiting_on) = unfold is_queue q {root; head;
      last; tail; retired_values; values; retired_fp; active_fp; retired_links;
      active_links; waiting; waiting_on} in
    is_queue_published_observe q new_tail (Finset.union retired_fp (Finset.union active_fp
      (Finset.singleton last))) (Finset.union retired_links active_links) (Finset.union
      retired_fp (Finset.singleton head)) waiting;
    segment_info root head retired_values retired_fp retired_links;
    segment_info head last values active_fp active_links;
    let exposure =
      if new_tail = last then At_last
      else if Finset.mem new_tail retired_fp then
        let (before, before_fp, before_links, value, next, after, after_fp, after_links) =
          segment_split root head retired_values retired_fp retired_links new_tail in
        Retired_cell (before, before_fp, before_links, value, next, after, after_fp,
          after_links)
      else
        let (before, before_fp, before_links, value, next, after, after_fp, after_links) =
          segment_split head last values active_fp active_links new_tail in
        Active_cell (before, before_fp, before_links, value, next, after, after_fp,
          after_links)
    in
    let result = step () in
    begin match exposure with
    | At_last -> ()
    | Retired_cell (before, before_fp, before_links, value, next, after, after_fp,
      after_links) ->
      segment_restore root new_tail next head before after before_fp after_fp before_links
        after_links value
    | Active_cell (before, before_fp, before_links, value, next, after, after_fp,
      after_links) ->
      segment_restore head new_tail next last before after before_fp after_fp before_links
        after_links value
    end;
    fold is_queue q;
    result) *)
    == Nil
    && not
         (Atomic.compare_and_set tail old_tail
            new_tail
            (*@ Ghost.scope (fun step ->
      let (root, head, last, cursor, retired_values, values, retired_fp, active_fp,
        retired_links, active_links, waiting, waiting_on) = unfold is_queue q {root; head;
        last; tail; retired_values; values; retired_fp; active_fp; retired_links;
        active_links; waiting; waiting_on} in
      is_queue_published_observe q new_tail (Finset.union retired_fp (Finset.union
        active_fp (Finset.singleton last))) (Finset.union retired_links active_links)
        (Finset.union retired_fp (Finset.singleton head)) waiting;
      let result = step () in
      fold is_queue q {tail = (if result then new_tail else cursor)};
      result) *))
  then fix_tail tail new_tail
(*@ Ghost.scope (fun invoke ->
    let result = invoke q in
    result) *)
(*@ manual *)
(*@ fix_tail [q : t] tail new_tail
    requires is_queue q && tail = q.tail
    requires own (Ghost.at facts_auth q.head)
      (Fact_auth.frag (Facts.set (Set.singleton (Published new_tail)))) *)

let push { tail; _ } value =
  let rec find_tail_and_enq curr_end node =
    if
      not
        (Atomic.compare_and_set curr_end Nil
           node
           (*@ Ghost.scope (fun step ->
      let (root, head, last, cursor, retired_values, values, retired_fp, active_fp,
        retired_links, active_links, waiting, waiting_on) = unfold is_queue q {root; head;
        last; tail; retired_values; values; retired_fp; active_fp; retired_links;
        active_links; waiting; waiting_on} in
      is_queue_published_observe q curr_end (Finset.union retired_fp (Finset.union
        active_fp (Finset.singleton last))) (Finset.union retired_links active_links)
        (Finset.union retired_fp (Finset.singleton head)) waiting;
      segment_info root head retired_values retired_fp retired_links;
      segment_info head last values active_fp active_links;
      let exposure =
        if curr_end = last then At_last
        else if Finset.mem curr_end retired_fp then
          let (before, before_fp, before_links, value, next, after, after_fp, after_links)
            =
            segment_split root head retired_values retired_fp retired_links curr_end in
          Retired_cell (before, before_fp, before_links, value, next, after, after_fp,
            after_links)
        else
          let (before, before_fp, before_links, value, next, after, after_fp, after_links)
            =
            segment_split head last values active_fp active_links curr_end in
          Active_cell (before, before_fp, before_links, value, next, after, after_fp,
            after_links)
      in
      let xs = Push.access token q value in
      unfold queue q xs;
      let result = step () in
      if result then begin
        assert (curr_end = last);
        segment_terminal_outside root head retired_values retired_fp retired_links fresh;
        segment_terminal_outside head last values active_fp active_links fresh;
        assert (fresh <> last);
        Ghost.write (Ghost.at view_queue q.head) (values @ [value]);
        fold queue q (values @ [value]);
        Push.commit token q value ();
        waiting_help q last (values @ [value]) waiting waiting_on
          (Set.of_predicate (fun (reg : Ghost.t) -> Map.get waiting_on reg <> last));
        segment_append head last fresh values active_fp active_links value;
        is_queue_fact_link q (Finset.union retired_fp (Finset.union active_fp
          (Finset.singleton last))) (Finset.union retired_links active_links)
          (Finset.union retired_fp (Finset.singleton head)) waiting last value fresh;
        is_queue_published_snapshot q
          (Finset.union (Finset.union retired_fp (Finset.union active_fp (Finset.singleton
            last))) (Finset.singleton fresh))
          (Finset.union (Finset.union retired_links active_links) (Finset.singleton (Edge
            (last, value, fresh))))
          (Finset.union retired_fp (Finset.singleton head)) waiting fresh;
        assert (Finset.union
          (Finset.union retired_fp (Finset.union active_fp (Finset.singleton last)))
          (Finset.singleton fresh) =
          Finset.union retired_fp
            (Finset.union (Finset.union active_fp (Finset.singleton last))
              (Finset.singleton fresh)));
        assert (Finset.union (Finset.union retired_links active_links)
          (Finset.singleton (Edge (last, value, fresh))) =
          Finset.union retired_links
            (Finset.union active_links (Finset.singleton (Edge (last, value, fresh)))));
        assert (facts_of
          (Finset.union
            (Finset.union retired_fp (Finset.union active_fp (Finset.singleton last)))
            (Finset.singleton fresh))
          (Finset.union (Finset.union retired_links active_links)
            (Finset.singleton (Edge (last, value, fresh))))
          (Finset.union retired_fp (Finset.singleton head)) waiting =
          facts_of
            (Finset.union retired_fp
              (Finset.union (Finset.union active_fp (Finset.singleton last))
                (Finset.singleton fresh)))
            (Finset.union retired_links
              (Finset.union active_links (Finset.singleton (Edge (last, value, fresh)))))
            (Finset.union retired_fp (Finset.singleton head)) waiting);
        fold is_queue q {last = fresh; values = (values @ [value]);
          active_fp = (Finset.union active_fp (Finset.singleton last));
          active_links = (Finset.union active_links
            (Finset.singleton (Edge (last, value, fresh))))}
      end else begin
      begin match exposure with
      | At_last -> ()
      | Retired_cell (before, before_fp, before_links, value, next, after, after_fp,
        after_links) ->
        segment_restore root curr_end next head before after before_fp after_fp
          before_links after_links value
      | Active_cell (before, before_fp, before_links, value, next, after, after_fp,
        after_links) ->
        segment_restore head curr_end next last before after before_fp after_fp
          before_links after_links value
      end;
      fold queue q xs;
      Push.abort token q value;
      fold is_queue q
      end;
      result) *))
    then
      match
        Atomic.get curr_end
        (*@ Ghost.scope (fun step ->
        let (root, head, last, cursor, retired_values, values, retired_fp, active_fp,
          retired_links, active_links, waiting, waiting_on) = unfold is_queue q {root;
          head; last; tail; retired_values; values; retired_fp; active_fp; retired_links;
          active_links; waiting; waiting_on} in
        is_queue_published_observe q curr_end (Finset.union retired_fp (Finset.union
          active_fp (Finset.singleton last))) (Finset.union retired_links active_links)
          (Finset.union retired_fp (Finset.singleton head)) waiting;
        segment_info root head retired_values retired_fp retired_links;
        segment_info head last values active_fp active_links;
        let exposure =
          if curr_end = last then At_last
          else if Finset.mem curr_end retired_fp then
            let (before, before_fp, before_links, value, next, after, after_fp,
              after_links) =
              segment_split root head retired_values retired_fp retired_links curr_end in
            Retired_cell (before, before_fp, before_links, value, next, after, after_fp,
              after_links)
          else
            let (before, before_fp, before_links, value, next, after, after_fp,
              after_links) =
              segment_split head last values active_fp active_links curr_end in
            Active_cell (before, before_fp, before_links, value, next, after, after_fp,
              after_links)
        in
        let result = step () in
        begin match exposure with
        | At_last -> ()
        | Retired_cell (before, before_fp, before_links, value, next, after, after_fp,
          after_links) ->
          segment_restore root curr_end next head before after before_fp after_fp
            before_links after_links value
        | Active_cell (before, before_fp, before_links, value, next, after, after_fp,
          after_links) ->
          segment_restore head curr_end next last before after before_fp after_fp
            before_links after_links value
        end;
        begin match result with
        | Nil -> ()
        | Next (_, next) ->
          consecutive_segment_edges root head last retired_values values retired_fp
            active_fp retired_links active_links;
          assert (Finset.mem next (Finset.union retired_fp (Finset.union active_fp
            (Finset.singleton last))));
          is_queue_published_snapshot q (Finset.union retired_fp (Finset.union active_fp
            (Finset.singleton last))) (Finset.union retired_links active_links)
            (Finset.union retired_fp (Finset.singleton head)) waiting next;
          ()
        end;
        fold is_queue q;
        result) *)
      with
      | Nil -> find_tail_and_enq curr_end node
      (*@ Ghost.scope (fun invoke ->
  let result = invoke (q, token, value, fresh) in
  result) *)
      | Next (_, n) -> find_tail_and_enq n node
    (*@ Ghost.scope (fun invoke ->
  let result = invoke (q, token, value, fresh) in
  result) *)
    (*@ find_tail_and_enq [q : t] [token : Push.token] [value : int]
          [fresh : node Atomic.t] curr_end node
        requires is_queue q
        requires min_int <= value && value <= max_int
        requires node = Next (value, fresh) && own fresh Nil
        requires own (Ghost.at facts_auth q.head)
          (Fact_auth.frag (Facts.set (Set.singleton (Published curr_end))))
        requires Push.pending token q value
        ensures Push.committed token q value ()
        ensures own (Ghost.at facts_auth q.head)
          (Fact_auth.frag (Facts.set (Set.singleton (Published fresh)))) *)
  in
  let new_tail = Atomic.make Nil in
  let newnode = Next (value, new_tail) in
  let old_tail =
    Atomic.get tail
    (*@ Ghost.State.scope (fun step () ->
    let token = Push.bind () in
    let (root, head, last, cursor, retired_values, values, retired_fp, active_fp,
      retired_links, active_links, waiting, waiting_on) = unfold is_queue q {root; head;
      last; tail; retired_values; values; retired_fp; active_fp; retired_links;
      active_links; waiting; waiting_on} in
    let result = step () in
    is_queue_published_snapshot q (Finset.union retired_fp (Finset.union active_fp
      (Finset.singleton last))) (Finset.union retired_links active_links) (Finset.union
      retired_fp (Finset.singleton head)) waiting result;
    fold is_queue q;
    (result, token)) *)
  in
  let linked =
    Atomic.compare_and_set old_tail Nil newnode
    (*@ Ghost.State.scope (fun step token ->
    let (root, head, last, cursor, retired_values, values, retired_fp, active_fp,
      retired_links, active_links, waiting, waiting_on) = unfold is_queue q {root; head;
      last; tail; retired_values; values; retired_fp; active_fp; retired_links;
      active_links; waiting; waiting_on} in
    is_queue_published_observe q old_tail (Finset.union retired_fp (Finset.union active_fp
      (Finset.singleton last))) (Finset.union retired_links active_links) (Finset.union
      retired_fp (Finset.singleton head)) waiting;
    segment_info root head retired_values retired_fp retired_links;
    segment_info head last values active_fp active_links;
    let exposure =
      if old_tail = last then At_last
      else if Finset.mem old_tail retired_fp then
        let (before, before_fp, before_links, value, next, after, after_fp, after_links) =
          segment_split root head retired_values retired_fp retired_links old_tail in
        Retired_cell (before, before_fp, before_links, value, next, after, after_fp,
          after_links)
      else
        let (before, before_fp, before_links, value, next, after, after_fp, after_links) =
          segment_split head last values active_fp active_links old_tail in
        Active_cell (before, before_fp, before_links, value, next, after, after_fp,
          after_links)
    in
    let xs = Push.access token q value in
    unfold queue q xs;
    let result = step () in
    if result then begin
      assert (old_tail = last);
      segment_terminal_outside root head retired_values retired_fp retired_links new_tail;
      segment_terminal_outside head last values active_fp active_links new_tail;
      assert (new_tail <> last);
      Ghost.write (Ghost.at view_queue q.head) (values @ [value]);
      fold queue q (values @ [value]);
      Push.commit token q value ();
      waiting_help q last (values @ [value]) waiting waiting_on
        (Set.of_predicate (fun (reg : Ghost.t) -> Map.get waiting_on reg <> last));
      segment_append head last new_tail values active_fp active_links value;
      is_queue_fact_link q (Finset.union retired_fp (Finset.union active_fp
        (Finset.singleton last))) (Finset.union retired_links active_links) (Finset.union
        retired_fp (Finset.singleton head)) waiting last value new_tail;
      is_queue_published_snapshot q
        (Finset.union (Finset.union retired_fp (Finset.union active_fp (Finset.singleton
          last))) (Finset.singleton new_tail))
        (Finset.union (Finset.union retired_links active_links) (Finset.singleton (Edge
          (last, value, new_tail))))
        (Finset.union retired_fp (Finset.singleton head)) waiting new_tail;
      assert (Finset.union
        (Finset.union retired_fp (Finset.union active_fp (Finset.singleton last)))
        (Finset.singleton new_tail) =
        Finset.union retired_fp
          (Finset.union (Finset.union active_fp (Finset.singleton last))
            (Finset.singleton new_tail)));
      assert (Finset.union (Finset.union retired_links active_links)
        (Finset.singleton (Edge (last, value, new_tail))) =
        Finset.union retired_links
          (Finset.union active_links (Finset.singleton (Edge (last, value, new_tail)))));
      assert (facts_of
        (Finset.union
          (Finset.union retired_fp (Finset.union active_fp (Finset.singleton last)))
          (Finset.singleton new_tail))
        (Finset.union (Finset.union retired_links active_links)
          (Finset.singleton (Edge (last, value, new_tail))))
        (Finset.union retired_fp (Finset.singleton head)) waiting =
        facts_of
          (Finset.union retired_fp
            (Finset.union (Finset.union active_fp (Finset.singleton last))
              (Finset.singleton new_tail)))
          (Finset.union retired_links
            (Finset.union active_links (Finset.singleton (Edge (last, value, new_tail)))))
          (Finset.union retired_fp (Finset.singleton head)) waiting);
      fold is_queue q {last = new_tail; values = (values @ [value]);
        active_fp = (Finset.union active_fp (Finset.singleton last));
        active_links = (Finset.union active_links
          (Finset.singleton (Edge (last, value, new_tail))))}
    end else begin
    begin match exposure with
    | At_last -> ()
    | Retired_cell (before, before_fp, before_links, value, next, after, after_fp,
      after_links) ->
      segment_restore root old_tail next head before after before_fp after_fp before_links
        after_links value
    | Active_cell (before, before_fp, before_links, value, next, after, after_fp,
      after_links) ->
      segment_restore head old_tail next last before after before_fp after_fp before_links
        after_links value
    end;
    fold queue q xs;
    Push.abort token q value;
    fold is_queue q
    end;
    (result, token)) *)
  in
  if not linked then
    begin match
      Atomic.get old_tail
      (*@ Ghost.scope (fun step ->
      let (root, head, last, cursor, retired_values, values, retired_fp, active_fp,
        retired_links, active_links, waiting, waiting_on) = unfold is_queue q {root; head;
        last; tail; retired_values; values; retired_fp; active_fp; retired_links;
        active_links; waiting; waiting_on} in
      is_queue_published_observe q old_tail (Finset.union retired_fp (Finset.union
        active_fp (Finset.singleton last))) (Finset.union retired_links active_links)
        (Finset.union retired_fp (Finset.singleton head)) waiting;
      segment_info root head retired_values retired_fp retired_links;
      segment_info head last values active_fp active_links;
      let exposure =
        if old_tail = last then At_last
        else if Finset.mem old_tail retired_fp then
          let (before, before_fp, before_links, value, next, after, after_fp, after_links)
            =
            segment_split root head retired_values retired_fp retired_links old_tail in
          Retired_cell (before, before_fp, before_links, value, next, after, after_fp,
            after_links)
        else
          let (before, before_fp, before_links, value, next, after, after_fp, after_links)
            =
            segment_split head last values active_fp active_links old_tail in
          Active_cell (before, before_fp, before_links, value, next, after, after_fp,
            after_links)
      in
      let result = step () in
      begin match exposure with
      | At_last -> ()
      | Retired_cell (before, before_fp, before_links, value, next, after, after_fp,
        after_links) ->
        segment_restore root old_tail next head before after before_fp after_fp
          before_links after_links value
      | Active_cell (before, before_fp, before_links, value, next, after, after_fp,
        after_links) ->
        segment_restore head old_tail next last before after before_fp after_fp
          before_links after_links value
      end;
      begin match result with
      | Nil -> ()
      | Next (_, next) ->
        consecutive_segment_edges root head last retired_values values retired_fp
          active_fp retired_links active_links;
        assert (Finset.mem next (Finset.union retired_fp (Finset.union active_fp
          (Finset.singleton last))));
        is_queue_published_snapshot q (Finset.union retired_fp (Finset.union active_fp
          (Finset.singleton last))) (Finset.union retired_links active_links)
          (Finset.union retired_fp (Finset.singleton head)) waiting next;
        ()
      end;
      fold is_queue q;
      result) *)
    with
    | Nil -> find_tail_and_enq old_tail newnode
    (*@ Ghost.State.scope (fun invoke token ->
  let result = invoke (q, token, value, new_tail) in
  (result, token)) *)
    | Next (_, n) -> find_tail_and_enq n newnode
    (*@ Ghost.State.scope (fun invoke token ->
  let result = invoke (q, token, value, new_tail) in
  (result, token)) *)
    end;
  if
    not
      (Atomic.compare_and_set tail old_tail
         new_tail
         (*@ Ghost.scope (fun step ->
    let (root, head, last, cursor, retired_values, values, retired_fp, active_fp,
      retired_links, active_links, waiting, waiting_on) = unfold is_queue q {root; head;
      last; tail; retired_values; values; retired_fp; active_fp; retired_links;
      active_links; waiting; waiting_on} in
    is_queue_published_observe q new_tail (Finset.union retired_fp (Finset.union active_fp
      (Finset.singleton last))) (Finset.union retired_links active_links) (Finset.union
      retired_fp (Finset.singleton head)) waiting;
    let result = step () in
    fold is_queue q {tail = (if result then new_tail else cursor)};
    result) *))
  then fix_tail tail new_tail
(*@ Ghost.scope (fun invoke ->
    let result = invoke q in
    result) *)
(*@ manual *)

let rec pop_opt q =
  let old_head =
    Atomic.get q.head
    (*@ Ghost.scope (fun step ->
      let (root, head, last, tail, retired_values, values,
           retired_fp, active_fp, retired_links, active_links,
           waiting, waiting_on) =
        unfold is_queue q {root; head; last; tail; retired_values; values;
          retired_fp; active_fp; retired_links; active_links; waiting;
          waiting_on} in
      let result = step () in
      is_queue_head_snapshot q
        (Finset.union retired_fp (Finset.union active_fp (Finset.singleton last)))
        (Finset.union retired_links active_links)
        (Finset.union retired_fp (Finset.singleton head)) waiting result;
      fold is_queue q;
      result) *)
  in
  match
    Atomic.get old_head
    (*@ Ghost.scope (fun step ->
      let (root, head, last, tail, retired_values, values,
           retired_fp, active_fp, retired_links, active_links,
           waiting, waiting_on) =
        unfold is_queue q {root; head; last; tail; retired_values; values;
          retired_fp; active_fp; retired_links; active_links; waiting;
          waiting_on} in
      is_queue_head_observe q old_head
        (Finset.union retired_fp (Finset.union active_fp (Finset.singleton last)))
        (Finset.union retired_links active_links)
        (Finset.union retired_fp (Finset.singleton head)) waiting;
      segment_info root head retired_values retired_fp retired_links;
      segment_info head last values active_fp active_links;
      let exposure =
        if old_head <> head then
          let (before, before_fp, before_links, value, next,
               after, after_fp, after_links) =
            segment_split root head retired_values retired_fp retired_links old_head in
          Retired_cell (before, before_fp, before_links, value, next,
            after, after_fp, after_links)
        else if old_head <> last then
          let (before, before_fp, before_links, value, next,
               after, after_fp, after_links) =
            segment_split head last values active_fp active_links old_head in
          Active_cell (before, before_fp, before_links, value, next,
            after, after_fp, after_links)
        else At_last
      in
      let result = step () in
      begin match exposure with
      | At_last -> ()
      | Retired_cell (before, before_fp, before_links, value, next,
          after, after_fp, after_links) ->
          segment_restore root old_head next head before after
            before_fp after_fp before_links after_links value
      | Active_cell (before, before_fp, before_links, value, next,
          after, after_fp, after_links) ->
          segment_restore head old_head next last before after
            before_fp after_fp before_links after_links value
      end;
      begin match result with
      | Nil ->
          let token = Pop.bind () in
          let xs = Pop.access token q in
          unfold queue q xs;
          assert (xs = []);
          fold queue q xs;
          Pop.commit token q None
      | Next (value, next) ->
          is_queue_link_snapshot q
            (Finset.union retired_fp (Finset.union active_fp (Finset.singleton last)))
            (Finset.union retired_links active_links)
            (Finset.union retired_fp (Finset.singleton head)) waiting
            (Edge (old_head, value, next))
      end;
      fold is_queue q;
      result) *)
  with
  | Nil -> None
  | Next (value, next) ->
      if
        Atomic.compare_and_set q.head old_head next
        (*@ Ghost.scope (fun step ->
          let (root, head, last, tail, retired_values, values,
               retired_fp, active_fp, retired_links, active_links,
               waiting, waiting_on) =
            unfold is_queue q {root; head; last; tail; retired_values; values;
              retired_fp; active_fp; retired_links; active_links; waiting;
              waiting_on} in
          let token = Pop.bind () in
          let xs = Pop.access token q in
          unfold queue q xs;
          assert (xs = values);
          is_queue_head_observe q old_head
            (Finset.union retired_fp (Finset.union active_fp (Finset.singleton last)))
            (Finset.union retired_links active_links)
            (Finset.union retired_fp (Finset.singleton head)) waiting;
          is_queue_link_observe q (Edge (old_head, value, next))
            (Finset.union retired_fp (Finset.union active_fp (Finset.singleton last)))
            (Finset.union retired_links active_links)
            (Finset.union retired_fp (Finset.singleton head)) waiting;
          consecutive_segment_edges root head last retired_values values
            retired_fp active_fp retired_links active_links;
          let result = step () in
          if result then begin
            assert (old_head = head);
            segment_info root head retired_values retired_fp retired_links;
            segment_edge_endpoints root head retired_values retired_fp retired_links;
            assert (not (Finset.mem old_head retired_fp));
            assert (not (Finset.mem (Edge (old_head, value, next)) retired_links));
            assert (Finset.mem (Edge (old_head, value, next)) active_links);
            segment_info head last values active_fp active_links;
            assert (values <> []);
            let (active_next, suffix_fp, suffix_links) =
              unfold segment head last values active_fp active_links
                {next; tail_cells; tail_edges} in
            assert (active_next = next);
            let (first, rest) =
              match values with
              | [] -> assert false
              | first :: rest -> (first, rest)
            in
            assert (first = value);
            segment_info next last rest suffix_fp suffix_links;
            assert (Finset.mem next (Finset.union suffix_fp (Finset.singleton last)));
            assert (not (Finset.mem last retired_fp));
            assert (Finset.inter suffix_fp retired_fp = Finset.empty);
            assert (next <> head && not (Finset.mem next retired_fp));
            Ghost.write (Ghost.at view_queue q.head) rest;
            fold queue q rest;
            Pop.commit token q (Some value);
            segment_append root head next retired_values retired_fp
              retired_links value;
            is_queue_fact_pop q
              (Finset.union retired_fp (Finset.union active_fp (Finset.singleton last)))
              (Finset.union retired_links active_links)
              (Finset.union retired_fp (Finset.singleton head)) waiting next;
            assert (active_fp = Finset.union suffix_fp (Finset.singleton head));
            assert (active_links = Finset.union suffix_links
              (Finset.singleton (Edge (head, value, next))));
            assert (Finset.union retired_fp
              (Finset.union active_fp (Finset.singleton last)) =
              Finset.union (Finset.union retired_fp (Finset.singleton head))
                (Finset.union suffix_fp (Finset.singleton last)));
            assert (Finset.union retired_links active_links =
              Finset.union (Finset.union retired_links
                (Finset.singleton (Edge (head, value, next)))) suffix_links);
            assert (facts_of
              (Finset.union retired_fp (Finset.union active_fp (Finset.singleton last)))
              (Finset.union retired_links active_links)
              (Finset.union (Finset.union retired_fp (Finset.singleton head))
                (Finset.singleton next)) waiting =
              facts_of
                (Finset.union (Finset.union retired_fp (Finset.singleton head))
                  (Finset.union suffix_fp (Finset.singleton last)))
                (Finset.union (Finset.union retired_links
                  (Finset.singleton (Edge (head, value, next)))) suffix_links)
                (Finset.union (Finset.union retired_fp (Finset.singleton head))
                  (Finset.singleton next)) waiting);
            fold is_queue q {head = next;
              retired_values = retired_values @ [value]; values = rest;
              retired_fp = Finset.union retired_fp (Finset.singleton head);
              active_fp = suffix_fp;
              retired_links = Finset.union retired_links
                (Finset.singleton (Edge (head, value, next)));
              active_links = suffix_links}
          end else begin
            fold queue q xs;
            Pop.abort token q;
            fold is_queue q
          end;
          result) *)
      then Some value
      else pop_opt q
(*@ Ghost.scope (fun invoke ->
          let token = Pop.bind () in
          let xs = Pop.access token q in
          let result = invoke () in
          Pop.commit token q result;
          result) *)
(*@ manual *)

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
      segment_info root head retired_values retired_fp retired_links;
      segment_info head last values active_fp active_links;
      let exposure =
        if old_tail = last then At_last
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
          segment_info head last values active_fp active_links;
          assert (Finset.mem next
            (Finset.union retired_fp
              (Finset.union active_fp (Finset.singleton last))));
          let result = step () in
          if result then
            fold is_queue q {tail = next}
          else
            fold is_queue q;
          result) *)
      then ()
      else ()
(*@ manual *)

let is_empty q =
  let old_head =
    Atomic.get q.head
    (*@ Ghost.State.scope (fun step () ->
      let token = Empty.bind () in
      let (root, head, last, tail, retired_values, values,
           retired_fp, active_fp, retired_links, active_links,
           waiting, waiting_on) =
        unfold is_queue q {root; head; last; tail; retired_values; values;
          retired_fp; active_fp; retired_links; active_links; waiting;
          waiting_on} in
      let result = step () in
      is_queue_head_snapshot q
        (Finset.union retired_fp (Finset.union active_fp (Finset.singleton last)))
        (Finset.union retired_links active_links)
        (Finset.union retired_fp (Finset.singleton head)) waiting result;
      let observation =
        if result <> last then begin
          segment_info head last values active_fp active_links;
          let (next, rest_fp, rest_links) =
            unfold segment head last values active_fp active_links
              {next; tail_cells; tail_edges} in
          let (value, rest) =
            match values with
            | [] -> assert false
            | value :: rest -> (value, rest)
          in
          fold segment head last values active_fp active_links
            {next = next; tail_cells = rest_fp; tail_edges = rest_links};
          let link = Edge (result, value, next) in
          is_queue_link_snapshot q
            (Finset.union retired_fp
              (Finset.union active_fp (Finset.singleton last)))
            (Finset.union retired_links active_links)
            (Finset.union retired_fp (Finset.singleton head)) waiting link;
          let xs = Empty.access token q in
          unfold queue q xs;
          assert (xs <> []);
          fold queue q xs;
          Empty.commit token q false;
          fold is_queue q;
          Observed_link link
        end else begin
          let registration = Ghost.alloc [
            Ghost.init waiting_watched result;
            Ghost.init waiting_linked false;
            Ghost.init waiting_token token;
            Ghost.init waiting_retired false
          ] in
          fold waiting_registration registration q
            {token = token; linked = false; retired = false};
          is_queue_fact_register q
            (Finset.union retired_fp (Finset.union active_fp (Finset.singleton last)))
            (Finset.union retired_links active_links)
            (Finset.union retired_fp (Finset.singleton head)) waiting registration;
          is_queue_registration_snapshot q
            (Finset.union retired_fp (Finset.union active_fp (Finset.singleton last)))
            (Finset.union retired_links active_links)
            (Finset.union retired_fp (Finset.singleton head))
            (Finset.union waiting (Finset.singleton registration)) registration;
          fold is_queue q {waiting = Finset.union waiting (Finset.singleton registration);
            waiting_on = Map.set waiting_on registration result};
          Waiting_on registration
        end
      in
      (result, observation)) *)
  in
  let observed =
    Atomic.get old_head
    (*@ Ghost.State.scope (fun step (observation : empty_observation) ->
    let (root, head, last, tail, retired_values, values,
         retired_fp, active_fp, retired_links, active_links,
         waiting, waiting_on) =
      unfold is_queue q {root; head; last; tail; retired_values; values;
        retired_fp; active_fp; retired_links; active_links; waiting;
        waiting_on} in
    is_queue_head_observe q old_head
      (Finset.union retired_fp (Finset.union active_fp (Finset.singleton last)))
      (Finset.union retired_links active_links)
      (Finset.union retired_fp (Finset.singleton head)) waiting;
    begin match observation with
    | Observed_link link ->
        is_queue_link_observe q link
          (Finset.union retired_fp (Finset.union active_fp (Finset.singleton last)))
          (Finset.union retired_links active_links)
          (Finset.union retired_fp (Finset.singleton head)) waiting
    | Waiting_on registration ->
        is_queue_registration_observe q registration
          (Finset.union retired_fp (Finset.union active_fp (Finset.singleton last)))
          (Finset.union retired_links active_links)
          (Finset.union retired_fp (Finset.singleton head)) waiting
    end;
    segment_info root head retired_values retired_fp retired_links;
    segment_info head last values active_fp active_links;
    let exposure =
      if old_head <> head then
        let (before, before_fp, before_links, value, next,
             after, after_fp, after_links) =
          segment_split root head retired_values retired_fp retired_links old_head in
        Retired_cell (before, before_fp, before_links, value, next,
          after, after_fp, after_links)
      else if old_head <> last then
        let (before, before_fp, before_links, value, next,
             after, after_fp, after_links) =
          segment_split head last values active_fp active_links old_head in
        Active_cell (before, before_fp, before_links, value, next,
          after, after_fp, after_links)
      else At_last
    in
    let result = step () in
    begin match exposure with
    | At_last -> ()
    | Retired_cell (before, before_fp, before_links, value, next,
        after, after_fp, after_links) ->
        segment_restore root old_head next head before after
          before_fp after_fp before_links after_links value
    | Active_cell (before, before_fp, before_links, value, next,
        after, after_fp, after_links) ->
        segment_restore head old_head next last before after
          before_fp after_fp before_links after_links value
    end;
    begin match observation with
    | Observed_link link ->
        consecutive_segment_edges root head last retired_values values
          retired_fp active_fp retired_links active_links;
        begin match result with
        | Nil -> assert false
        | Next (_, _) -> ()
        end
    | Waiting_on registration ->
        assert (Map.get waiting_on registration = old_head);
        let (token, linked, retired) =
          unfold waiting_registration registration q {token; linked; retired} in
        begin match result with
        | Nil ->
            let xs = Empty.access token q in
            unfold queue q xs;
            assert (xs = []);
            fold queue q xs;
            Empty.commit token q true
        | Next (_, _) -> assert linked
        end;
        Ghost.write (Ghost.at waiting_retired registration) true;
        fold waiting_registration registration q
          {token = token; linked = linked; retired = true}
    end;
    fold is_queue q;
    (result, observation)) *)
  in
  observed == Nil
(*@ manual *)
