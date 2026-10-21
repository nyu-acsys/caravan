(** The errors Caravan reports itself, which it prints as Raven prints its own. *)

open Base
module R = Raven_api

type kind = Syntax | Type | Unsupported

type error = {
  kind : kind;
  loc : Location.t;
  message : string;
  related : (Location.t * string) list;
}

let error ?(related = []) kind loc message = { kind; loc; message; related }
let loc (l : Location.t) = R.Loc.make l.loc_start l.loc_end
let text doc = Format_doc.asprintf "%a" Format_doc.pp_doc doc

(** The error the compiler's front end reports with [exn], if it is one. *)
let of_exn (exn : exn) : error option =
  let kind = match exn with Syntaxerr.Error _ | Lexer.Error _ -> Syntax | _ -> Type in
  match Location.error_of_exn exn with
  | Some (`Ok report) ->
      Some
        {
          kind;
          loc = report.main.loc;
          message = text report.main.txt;
          related =
            List.map report.sub ~f:(fun (msg : Location.msg) -> (msg.loc, text msg.txt));
        }
  | Some `Already_displayed | None -> None

let to_diagnostic (e : error) : R.Diagnostic.t =
  {
    severity = Error;
    kind =
      (match e.kind with Syntax -> Syntax | Type -> Type | Unsupported -> Unsupported);
    code = None;
    loc = loc e.loc;
    message = e.message;
    related =
      List.map e.related ~f:(fun (l, message) ->
          { R.Diagnostic.related_loc = loc l; related_message = message });
  }

let print_diagnostic (d : R.Diagnostic.t) =
  match d.severity with
  | Warning -> Logs.warn (fun m -> m "%s" (R.Diagnostic.to_string d))
  | Error -> Logs.err (fun m -> m "%s" (R.Diagnostic.to_string d))

let print (e : error) = print_diagnostic (to_diagnostic e)
let unsupported loc what = Error (error Unsupported loc (what ^ " is not supported yet"))
