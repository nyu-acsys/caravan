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
    let s = unfold is_queue q in
    observe_fact q s (Published new_tail);
    segment_info s.root s.head;
    segment_info s.head s.last;
    let exposure =
      if new_tail == s.last then At_last
      else if Finset.mem new_tail s.retired_fp then
        let (before, before_fp, before_links, value, next, after, after_fp, after_links) =
          segment_split s.root s.head s.retired_values s.retired_fp s.retired_links new_tail in
        Retired_cell (before, before_fp, before_links, value, next, after, after_fp,
          after_links)
      else
        let (before, before_fp, before_links, value, next, after, after_fp, after_links) =
          segment_split s.head s.last s.values s.active_fp s.active_links new_tail in
        Active_cell (before, before_fp, before_links, value, next, after, after_fp,
          after_links)
    in
    let result = step () in
    begin match exposure with
    | At_last -> ()
    | Retired_cell (before, before_fp, before_links, value, next, after, after_fp,
      after_links) ->
      segment_restore s.root new_tail next s.head before after before_fp after_fp before_links
        after_links value
    | Active_cell (before, before_fp, before_links, value, next, after, after_fp,
      after_links) ->
      segment_restore s.head new_tail next s.last before after before_fp after_fp before_links
        after_links value
    end;
    fold is_queue q;
    result) *)
    == Nil
    && not
         (Atomic.compare_and_set tail old_tail
            new_tail
            (*@ Ghost.scope (fun step ->
      let s = unfold is_queue q in
      observe_fact q s (Published new_tail);
      let result = step () in
      fold is_queue q {tail = (if result then new_tail else s.tail)};
      result) *))
  then fix_tail tail new_tail
(*@ Ghost.scope (fun invoke ->
    let result = invoke q in
    result) *)
(*@ manual *)
(*@ fix_tail [q : t] tail new_tail
    requires is_queue q && tail == q.tail
    requires own (Ghost.at facts_auth q.head)
      (Fact_auth.frag (Facts.set (Set.singleton (Published new_tail)))) *)

let push { tail; _ } value =
  let rec find_tail_and_enq curr_end node =
    if
      not
        (Atomic.compare_and_set curr_end Nil
           node
           (*@ Ghost.scope (fun step ->
      let s = unfold is_queue q in
      observe_fact q s (Published curr_end);
      segment_info s.root s.head;
      segment_info s.head s.last;
      let exposure =
        if curr_end == s.last then At_last
        else if Finset.mem curr_end s.retired_fp then
          let (before, before_fp, before_links, value, next, after, after_fp, after_links)
            =
            segment_split s.root s.head s.retired_values s.retired_fp s.retired_links curr_end in
          Retired_cell (before, before_fp, before_links, value, next, after, after_fp,
            after_links)
        else
          let (before, before_fp, before_links, value, next, after, after_fp, after_links)
            =
            segment_split s.head s.last s.values s.active_fp s.active_links curr_end in
          Active_cell (before, before_fp, before_links, value, next, after, after_fp,
            after_links)
      in
      let xs = Push.access token q value in
      unfold queue q xs;
      let result = step () in
      if result then begin
        assert (curr_end == s.last);
        segment_terminal_outside s.root s.head s.retired_values s.retired_fp s.retired_links fresh;
        segment_terminal_outside s.head s.last s.values s.active_fp s.active_links fresh;
        assert (fresh != s.last);
        Ghost.write (Ghost.at view_queue q.head) (s.values @ [value]);
        fold queue q (s.values @ [value]);
        Push.commit token q value ();
        waiting_help q s.last (s.values @ [value]) s.waiting s.waiting_on
          (Set.of_predicate (fun (reg : Ghost.t) -> Map.get s.waiting_on reg != s.last));
        segment_append s.head s.last fresh s.values s.active_fp s.active_links value;
        let s' = { s with last = fresh; values = s.values @ [value];
          active_fp = Finset.union s.active_fp (Finset.singleton s.last);
          active_links = Finset.union s.active_links
            (Finset.singleton (Edge (s.last, value, fresh))) } in
        grow_facts q s s';
        issue_fact q s' (Published fresh);
        fold is_queue q s'
      end else begin
      begin match exposure with
      | At_last -> ()
      | Retired_cell (before, before_fp, before_links, value, next, after, after_fp,
        after_links) ->
        segment_restore s.root curr_end next s.head before after before_fp after_fp
          before_links after_links value
      | Active_cell (before, before_fp, before_links, value, next, after, after_fp,
        after_links) ->
        segment_restore s.head curr_end next s.last before after before_fp after_fp
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
        let s = unfold is_queue q in
        observe_fact q s (Published curr_end);
        segment_info s.root s.head;
        segment_info s.head s.last;
        let exposure =
          if curr_end == s.last then At_last
          else if Finset.mem curr_end s.retired_fp then
            let (before, before_fp, before_links, value, next, after, after_fp,
              after_links) =
              segment_split s.root s.head s.retired_values s.retired_fp s.retired_links curr_end in
            Retired_cell (before, before_fp, before_links, value, next, after, after_fp,
              after_links)
          else
            let (before, before_fp, before_links, value, next, after, after_fp,
              after_links) =
              segment_split s.head s.last s.values s.active_fp s.active_links curr_end in
            Active_cell (before, before_fp, before_links, value, next, after, after_fp,
              after_links)
        in
        let result = step () in
        begin match exposure with
        | At_last -> ()
        | Retired_cell (before, before_fp, before_links, value, next, after, after_fp,
          after_links) ->
          segment_restore s.root curr_end next s.head before after before_fp after_fp
            before_links after_links value
        | Active_cell (before, before_fp, before_links, value, next, after, after_fp,
          after_links) ->
          segment_restore s.head curr_end next s.last before after before_fp after_fp
            before_links after_links value
        end;
        begin match result with
        | Nil -> ()
        | Next (_, next) ->
          consecutive_segment_edges s.root s.head s.last s.retired_values s.values s.retired_fp
            s.active_fp s.retired_links s.active_links;
          issue_fact q s (Published next);
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
        requires node === Next (value, fresh) && own fresh Nil
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
    let s = unfold is_queue q in
    let result = step () in
    issue_fact q s (Published result);
    fold is_queue q;
    (result, token)) *)
  in
  if
    not
      (Atomic.compare_and_set old_tail Nil
         newnode
         (*@ Ghost.scope (fun step ->
    let token = Push.bind () in
    let s = unfold is_queue q in
    observe_fact q s (Published old_tail);
    segment_info s.root s.head;
    segment_info s.head s.last;
    let exposure =
      if old_tail == s.last then At_last
      else if Finset.mem old_tail s.retired_fp then
        let (before, before_fp, before_links, value, next, after, after_fp, after_links) =
          segment_split s.root s.head s.retired_values s.retired_fp s.retired_links old_tail in
        Retired_cell (before, before_fp, before_links, value, next, after, after_fp,
          after_links)
      else
        let (before, before_fp, before_links, value, next, after, after_fp, after_links) =
          segment_split s.head s.last s.values s.active_fp s.active_links old_tail in
        Active_cell (before, before_fp, before_links, value, next, after, after_fp,
          after_links)
    in
    let xs = Push.access token q value in
    unfold queue q xs;
    let result = step () in
    if result then begin
      assert (old_tail == s.last);
      segment_terminal_outside s.root s.head s.retired_values s.retired_fp s.retired_links new_tail;
      segment_terminal_outside s.head s.last s.values s.active_fp s.active_links new_tail;
      assert (new_tail != s.last);
      Ghost.write (Ghost.at view_queue q.head) (s.values @ [value]);
      fold queue q (s.values @ [value]);
      Push.commit token q value ();
      waiting_help q s.last (s.values @ [value]) s.waiting s.waiting_on
        (Set.of_predicate (fun (reg : Ghost.t) -> Map.get s.waiting_on reg != s.last));
      segment_append s.head s.last new_tail s.values s.active_fp s.active_links value;
      let s' = { s with last = new_tail; values = s.values @ [value];
        active_fp = Finset.union s.active_fp (Finset.singleton s.last);
        active_links = Finset.union s.active_links
          (Finset.singleton (Edge (s.last, value, new_tail))) } in
      grow_facts q s s';
      issue_fact q s' (Published new_tail);
      fold is_queue q s'
    end else begin
    begin match exposure with
    | At_last -> ()
    | Retired_cell (before, before_fp, before_links, value, next, after, after_fp,
      after_links) ->
      segment_restore s.root old_tail next s.head before after before_fp after_fp before_links
        after_links value
    | Active_cell (before, before_fp, before_links, value, next, after, after_fp,
      after_links) ->
      segment_restore s.head old_tail next s.last before after before_fp after_fp before_links
        after_links value
    end;
    fold queue q xs;
    Push.abort token q value;
    fold is_queue q
    end;
    result) *))
  then
    begin match
      Atomic.get old_tail
      (*@ Ghost.scope (fun step ->
      let s = unfold is_queue q in
      observe_fact q s (Published old_tail);
      segment_info s.root s.head;
      segment_info s.head s.last;
      let exposure =
        if old_tail == s.last then At_last
        else if Finset.mem old_tail s.retired_fp then
          let (before, before_fp, before_links, value, next, after, after_fp, after_links)
            =
            segment_split s.root s.head s.retired_values s.retired_fp s.retired_links old_tail in
          Retired_cell (before, before_fp, before_links, value, next, after, after_fp,
            after_links)
        else
          let (before, before_fp, before_links, value, next, after, after_fp, after_links)
            =
            segment_split s.head s.last s.values s.active_fp s.active_links old_tail in
          Active_cell (before, before_fp, before_links, value, next, after, after_fp,
            after_links)
      in
      let result = step () in
      begin match exposure with
      | At_last -> ()
      | Retired_cell (before, before_fp, before_links, value, next, after, after_fp,
        after_links) ->
        segment_restore s.root old_tail next s.head before after before_fp after_fp
          before_links after_links value
      | Active_cell (before, before_fp, before_links, value, next, after, after_fp,
        after_links) ->
        segment_restore s.head old_tail next s.last before after before_fp after_fp
          before_links after_links value
      end;
      begin match result with
      | Nil -> ()
      | Next (_, next) ->
        consecutive_segment_edges s.root s.head s.last s.retired_values s.values s.retired_fp
          s.active_fp s.retired_links s.active_links;
        issue_fact q s (Published next);
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
    let s = unfold is_queue q in
    observe_fact q s (Published new_tail);
    let result = step () in
    fold is_queue q {tail = (if result then new_tail else s.tail)};
    result) *))
  then fix_tail tail new_tail
(*@ Ghost.scope (fun invoke ->
    let result = invoke q in
    result) *)
(*@ manual *)

let rec pop_as q backoff =
  let old_head =
    Atomic.get q.head
    (*@ Ghost.scope (fun step ->
      let s = unfold is_queue q in
      let result = step () in
      issue_fact q s (Head_seen result);
      fold is_queue q;
      result) *)
  in
  match
    Atomic.get old_head
    (*@ Ghost.scope (fun step ->
      let s = unfold is_queue q in
      observe_fact q s (Head_seen old_head);
      segment_info s.root s.head;
      segment_info s.head s.last;
      let exposure =
        if old_head != s.head then
          let (before, before_fp, before_links, value, next,
               after, after_fp, after_links) =
            segment_split s.root s.head s.retired_values s.retired_fp s.retired_links old_head in
          Retired_cell (before, before_fp, before_links, value, next,
            after, after_fp, after_links)
        else if old_head != s.last then
          let (before, before_fp, before_links, value, next,
               after, after_fp, after_links) =
            segment_split s.head s.last s.values s.active_fp s.active_links old_head in
          Active_cell (before, before_fp, before_links, value, next,
            after, after_fp, after_links)
        else At_last
      in
      let result = step () in
      begin match exposure with
      | At_last -> ()
      | Retired_cell (before, before_fp, before_links, value, next,
          after, after_fp, after_links) ->
          segment_restore s.root old_head next s.head before after
            before_fp after_fp before_links after_links value
      | Active_cell (before, before_fp, before_links, value, next,
          after, after_fp, after_links) ->
          segment_restore s.head old_head next s.last before after
            before_fp after_fp before_links after_links value
      end;
      begin match result with
      | Nil ->
          let token = Pop.bind () in
          let xs = Pop.access token q initial_backoff in
          unfold queue q xs;
          assert (xs = []);
          fold queue q xs;
          Pop.commit token q initial_backoff None
      | Next (value, next) ->
          issue_fact q s (Linked (Edge (old_head, value, next)))
      end;
      fold is_queue q;
      result) *)
  with
  | Nil -> None
  | Next (value, next) ->
      if
        Atomic.compare_and_set q.head old_head next
        (*@ Ghost.scope (fun step ->
          let s = unfold is_queue q in
          let token = Pop.bind () in
          let xs = Pop.access token q initial_backoff in
          unfold queue q xs;
          assert (xs = s.values);
          observe_fact q s (Head_seen old_head);
          observe_fact q s (Linked (Edge (old_head, value, next)));
          consecutive_segment_edges s.root s.head s.last s.retired_values s.values
            s.retired_fp s.active_fp s.retired_links s.active_links;
          let result = step () in
          if result then begin
            assert (old_head == s.head);
            segment_info s.root s.head;
            segment_edge_endpoints s.root s.head s.retired_values s.retired_fp s.retired_links;
            segment_info s.head s.last;
            assert (s.values <> []);
            let (active_next, suffix_fp, suffix_links) =
              unfold segment s.head s.last s.values s.active_fp s.active_links
                {next; tail_cells; tail_edges} in
            assert (active_next == next);
            let (first, rest) =
              match s.values with
              | [] -> assert false
              | first :: rest -> (first, rest)
            in
            assert (first = value);
            segment_info next s.last;
            Ghost.write (Ghost.at view_queue q.head) rest;
            fold queue q rest;
            Pop.commit token q initial_backoff (Some value);
            segment_append s.root s.head next s.retired_values s.retired_fp
              s.retired_links value;
            let s' = { s with head = next; retired_values = s.retired_values @ [value];
              values = rest; retired_fp = Finset.union s.retired_fp (Finset.singleton s.head);
              active_fp = suffix_fp;
              retired_links = Finset.union s.retired_links
                (Finset.singleton (Edge (s.head, value, next)));
              active_links = suffix_links } in
            grow_facts q s s';
            fold is_queue q s'
          end else begin
            fold queue q xs;
            Pop.abort token q initial_backoff;
            fold is_queue q
          end;
          result) *)
      then Some value
      else
        let backoff = Backoff.once backoff in
        pop_as q backoff
(*@ Ghost.scope (fun invoke ->
          let token = Pop.bind () in
          let xs = Pop.access token q initial_backoff in
          let result = invoke () in
          Pop.commit token q initial_backoff result;
          result) *)
(*@ manual *)

(*@ result = atomic pop_as q initial_backoff
    requires is_queue q
    atomic requires queue q xs
    atomic ensures match xs with
      | [] -> result = None && queue q []
      | value :: rest -> result = Some value && queue q rest *)

let pop_opt q = pop_as q Backoff.default
(*@ Ghost.scope (fun invoke ->
    let token = PopOpt.bind () in
    let xs = PopOpt.access token q in
    let result = invoke () in
    PopOpt.commit token q result;
    result) *)
(*@ manual *)

let is_empty { head; _ } =
  Atomic.get
    (Atomic.get
       head
       (*@ Ghost.State.scope (fun step () ->
      let token = Empty.bind () in
      let s = unfold is_queue q in
      let result = step () in
      issue_fact q s (Head_seen result);
      let observation =
        if result != s.last then begin
          segment_info s.head s.last;
          let (next, rest_fp, rest_links) =
            unfold segment s.head s.last s.values s.active_fp s.active_links
              {next; tail_cells; tail_edges} in
          let (value, rest) =
            match s.values with
            | [] -> assert false
            | value :: rest -> (value, rest)
          in
          fold segment s.head s.last s.values s.active_fp s.active_links
            {next = next; tail_cells = rest_fp; tail_edges = rest_links};
          let link = Edge (result, value, next) in
          issue_fact q s (Linked link);
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
          let s' = { s with waiting = Finset.union s.waiting (Finset.singleton registration);
            waiting_on = Map.set s.waiting_on registration result } in
          grow_facts q s s';
          issue_fact q s' (Registered registration);
          fold is_queue q s';
          Waiting_on registration
        end
      in
      (result, (result, observation))) *))
  (*@ Ghost.State.scope (fun step (old_head, observation) ->
    let s = unfold is_queue q in
    observe_fact q s (Head_seen old_head);
    begin match observation with
    | Observed_link link ->
        observe_fact q s (Linked link)
    | Waiting_on registration ->
        observe_fact q s (Registered registration)
    end;
    segment_info s.root s.head;
    segment_info s.head s.last;
    let exposure =
      if old_head != s.head then
        let (before, before_fp, before_links, value, next,
             after, after_fp, after_links) =
          segment_split s.root s.head s.retired_values s.retired_fp s.retired_links old_head in
        Retired_cell (before, before_fp, before_links, value, next,
          after, after_fp, after_links)
      else if old_head != s.last then
        let (before, before_fp, before_links, value, next,
             after, after_fp, after_links) =
          segment_split s.head s.last s.values s.active_fp s.active_links old_head in
        Active_cell (before, before_fp, before_links, value, next,
          after, after_fp, after_links)
      else At_last
    in
    let result = step () in
    begin match exposure with
    | At_last -> ()
    | Retired_cell (before, before_fp, before_links, value, next,
        after, after_fp, after_links) ->
        segment_restore s.root old_head next s.head before after
          before_fp after_fp before_links after_links value
    | Active_cell (before, before_fp, before_links, value, next,
        after, after_fp, after_links) ->
        segment_restore s.head old_head next s.last before after
          before_fp after_fp before_links after_links value
    end;
    begin match observation with
    | Observed_link link ->
        consecutive_segment_edges s.root s.head s.last s.retired_values s.values
          s.retired_fp s.active_fp s.retired_links s.active_links;
        begin match result with
        | Nil -> assert false
        | Next (_, _) -> ()
        end
    | Waiting_on registration ->
        assert (Map.get s.waiting_on registration == old_head);
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
    (result, ())) *)
  == Nil
(*@ manual *)

let of_list list =
  let tail_ = Atomic.make Nil in
  let tail = Atomic.make_contended tail_ in
  let rec build_next = function
    | [] -> tail_
    | hd :: tl -> Atomic.make @@ Next (hd, build_next tl)
    (*@ proof match xs with
    | [] -> fold segment result tail_ [] Finset.empty Finset.empty
    | hd :: tl -> segment_prepend result tail_ hd tl *)
    (*@ result = build_next xs
      requires own tail_ Nil
      ensures own tail_ Nil && segment result tail_ xs *)
  in
  let head =
    Atomic.make_contended @@ build_next list
    (*@ initializes [Ghost.init view_queue list;
      Ghost.init facts_auth (Fact_auth.full (Facts.set Set.empty))] *)
  in
  { head; tail }
(*@ proof initialize_built_queue q tail_ list *)
(*@ manual *)
