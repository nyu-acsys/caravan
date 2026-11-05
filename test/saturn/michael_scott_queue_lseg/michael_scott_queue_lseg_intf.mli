(*
 * Copyright (c) 2015, Théo Laurent <theo.laurent@ens.fr>
 * Copyright (c) 2015, KC Sivaramakrishnan <sk826@cl.cam.ac.uk>
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *)

module type MS_QUEUE = sig
  (** {1 API} *)

  type 'a t
  (** Represents a lock-free queue holding elements of type ['a]. *)
  (*@ invariant is_queue (q : 'a t) *)
  (*@ predicate queue (q : 'a t) (xs [@implicit] : 'a list) *)

  val create : unit -> 'a t
  (** [create ()] returns a new queue, initially empty. *)
  (*@ q = create () ensures is_queue q && queue q [] *)

  val of_list : 'a list -> 'a t
  (** [of_list list] creates a new queue from a list.

      🐌 This is a linear-time operation.

      {[
        # open Saturn.Queue
        # let t : int t = of_list [1;2;3;4]
        val t : int t = <abstr>
        # pop_opt t
        - : int option = Some 1
        # pop_opt t
        - : int option = Some 2
      ]} *)
  (*@ q = of_list list ensures is_queue q && queue q list *)

  val is_empty : 'a t -> bool
  (** [is_empty q] returns [true] if [q] is empty and [false] otherwise. *)
  (*@ result = atomic is_empty q requires is_queue q
      atomic requires queue q xs
      atomic ensures queue q xs && result = (xs === []) *)

  (** {2 Consumer functions} *)

  val pop_opt : 'a t -> 'a option
  (** [pop_opt q] removes and returns the first element in queue [q], or returns
      [None] if the queue is empty. *)
  (*@ result = atomic pop_opt q requires is_queue q
      atomic requires queue q xs
      atomic ensures match xs with
        | [] -> result === None && queue q []
        | value :: rest -> result === Some value && queue q rest *)

  (** {2 Producer functions} *)

  val push : 'a t -> 'a -> unit
  (** [push q v] adds the element [v] at the end of the queue [q]. *)
  (*@ atomic push q value requires is_queue q
      atomic requires queue q xs
      atomic ensures queue q (xs @ [value]) *)

end
