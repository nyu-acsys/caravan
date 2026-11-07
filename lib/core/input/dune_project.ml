open Base

type t = { interfaces : string list; dependencies : string list }

let empty = { interfaces = []; dependencies = [] }
let ( let* ) value f = Result.bind value ~f

(* Dune's csexp encoding has only lists and length-prefixed atoms. *)
let parse_csexp text =
  let length = String.length text in
  let rec value depth offset =
    if depth > 64 || offset >= length then Error "invalid csexp nesting or end of input"
    else if Char.equal text.[offset] '(' then list (depth + 1) (offset + 1) []
    else if Char.is_digit text.[offset] then atom offset offset
    else Error "invalid csexp token"
  and atom start offset =
    if offset >= length then Error "unterminated csexp atom"
    else if Char.equal text.[offset] ':' then
      let* size =
        match Int.of_string_opt (String.sub text ~pos:start ~len:(offset - start)) with
        | Some size when size >= 0 && size <= length - offset - 1 -> Ok size
        | _ -> Error "invalid csexp atom length"
      in
      let start = offset + 1 in
      Ok (Sexp.Atom (String.sub text ~pos:start ~len:size), start + size)
    else if Char.is_digit text.[offset] && offset - start < 12 then atom start (offset + 1)
    else Error "invalid csexp atom length"
  and list depth offset reversed =
    if offset >= length then Error "unterminated csexp list"
    else if Char.equal text.[offset] ')' then
      Ok (Sexp.List (List.rev reversed), offset + 1)
    else
      let* item, next = value depth offset in
      list depth next (item :: reversed)
  in
  if length > 16_000_000 then Error "Dune description is too large"
  else
    let* sexp, next = value 0 0 in
    if next = length then Ok sexp else Error "trailing csexp data"

let field key fields =
  List.find_map fields ~f:(function
    | Sexp.List [ Sexp.Atom name; value ] when String.equal name key -> Some value
    | _ -> None)

let atom = function Sexp.Atom value -> Some value | _ -> None
let fields = function Sexp.List fields -> Some fields | _ -> None
let string_field key fields = Option.bind (field key fields) ~f:atom
let strings = function Sexp.List values -> List.filter_map values ~f:atom | _ -> []

let path_field key fields =
  match field key fields with
  | Some (Sexp.List [ Sexp.Atom path ]) -> Some path
  | _ -> None

type module_info = {
  name : string;
  impl : string option;
  intf : string option;
  cmt : string option;
}

type library = {
  uid : string;
  local : bool;
  requires : string list;
  modules : module_info list;
}

type owner = { requires : string list; modules : module_info list }

let parse_module sexp =
  Option.bind (fields sexp) ~f:(fun fields ->
      Option.map (string_field "name" fields) ~f:(fun name ->
          {
            name;
            impl = path_field "impl" fields;
            intf = path_field "intf" fields;
            cmt = path_field "cmt" fields;
          }))

let parse_modules fields =
  match field "modules" fields with
  | Some (Sexp.List modules) -> List.filter_map modules ~f:parse_module
  | _ -> []

let parse_requires fields =
  Option.value_map (field "requires" fields) ~default:[] ~f:strings

let parse_library fields =
  match (string_field "uid" fields, string_field "local" fields) with
  | Some uid, Some local ->
      Some
        {
          uid;
          local = String.equal local "true";
          requires = parse_requires fields;
          modules = parse_modules fields;
        }
  | _ -> None

let native_path ?(windows = Stdlib.Sys.win32) path =
  if windows then String.map path ~f:(fun c -> if Char.equal c '/' then '\\' else c)
  else path

let comparable ?(windows = Stdlib.Sys.win32) path =
  let path = native_path ~windows path in
  if windows then Stdlib.String.lowercase_ascii path else path

let path_equal ?(windows = Stdlib.Sys.win32) left right =
  String.equal (comparable ~windows left) (comparable ~windows right)

let relative_to ?(windows = Stdlib.Sys.win32) ~root path =
  let root = native_path ~windows root in
  let path = native_path ~windows path in
  let separator = if windows then "\\" else Stdlib.Filename.dir_sep in
  let prefix =
    if String.is_suffix root ~suffix:separator then root else root ^ separator
  in
  if path_equal ~windows path root then Some ""
  else if String.is_prefix (comparable ~windows path) ~prefix:(comparable ~windows prefix)
  then Some (String.drop_prefix path (String.length prefix))
  else None

let absolute ~root path =
  let path = native_path path in
  if Stdlib.Filename.is_relative path then Stdlib.Filename.concat root path else path

let canonical_if_exists path =
  if Stdlib.Sys.file_exists path then Unix.realpath path else path

let original_path ~root ~build_context path =
  let path = native_path path in
  match relative_to ~root:(native_path build_context) path with
  | Some source -> canonical_if_exists (Stdlib.Filename.concat root source)
  | None -> canonical_if_exists (absolute ~root path)

let selected_interface ~root ~build_context ~build_directory ~file info =
  Option.bind info.intf ~f:(fun path ->
      let original = original_path ~root ~build_context path in
      let built =
        match relative_to ~root:(native_path build_context) (native_path path) with
        | Some source ->
            Stdlib.Filename.concat
              (Stdlib.Filename.concat build_directory
                 (Stdlib.Filename.basename (native_path build_context)))
              source
        | None -> absolute ~root path
      in
      if
        path_equal
          (Stdlib.Filename.remove_extension original)
          (Stdlib.Filename.remove_extension file)
      then None
      else if Stdlib.Sys.file_exists original then Some original
      else if Stdlib.Sys.file_exists built then Some (canonical_if_exists built)
      else None)

let dedup values =
  List.dedup_and_sort values ~compare:(fun left right ->
      String.compare (comparable left) (comparable right))

let is_wrapped_member info =
  Option.value_map info.cmt ~default:false ~f:(fun cmt ->
      let basename = Stdlib.Filename.basename (native_path cmt) in
      let logical = Stdlib.String.uncapitalize_ascii info.name ^ ".cmt" in
      not (path_equal basename logical))

let select ?build_directory ~root ~file sexp =
  let build_directory =
    Option.value build_directory ~default:(Stdlib.Filename.concat root "_build")
  in
  let* entries =
    match sexp with
    | Sexp.List entries -> Ok entries
    | _ -> Error "invalid Dune workspace description"
  in
  let build_context =
    List.find_map entries ~f:(function
      | Sexp.List [ Sexp.Atom "build_context"; Sexp.Atom path ] -> Some path
      | _ -> None)
    |> Option.value ~default:"_build/default"
  in
  let candidates =
    List.filter_map entries ~f:(function
      | Sexp.List [ Sexp.Atom ("library" | "executables"); Sexp.List fields ] ->
          let owner =
            { requires = parse_requires fields; modules = parse_modules fields }
          in
          Some owner
      | _ -> None)
  in
  let matches info =
    List.exists [ info.impl; info.intf ] ~f:(function
      | Some path -> path_equal (original_path ~root ~build_context path) file
      | None -> false)
  in
  let owners =
    List.filter candidates ~f:(fun owner -> List.exists owner.modules ~f:matches)
  in
  match owners with
  | [] -> Ok []
  | [ owner ] ->
      let libraries =
        List.filter_map entries ~f:(function
          | Sexp.List [ Sexp.Atom "library"; Sexp.List fields ] -> parse_library fields
          | _ -> None)
      in
      let rec closure seen = function
        | [] -> seen
        | uid :: rest when List.mem seen uid ~equal:String.equal -> closure seen rest
        | uid :: rest ->
            let dependencies =
              List.find_map libraries ~f:(fun library ->
                  Option.some_if (String.equal library.uid uid) library.requires)
              |> Option.value ~default:[]
            in
            closure (uid :: seen) (dependencies @ rest)
      in
      let required = closure [] owner.requires in
      let modules =
        owner.modules
        @ List.concat_map libraries ~f:(fun library ->
            if library.local && List.mem required library.uid ~equal:String.equal then
              library.modules
            else [])
      in
      let selected =
        List.filter_map modules
          ~f:(selected_interface ~root ~build_context ~build_directory ~file)
      in
      let wrapped =
        List.find modules ~f:(fun info ->
            Option.is_some
              (selected_interface ~root ~build_context ~build_directory ~file info)
            && is_wrapped_member info)
      in
      begin match wrapped with
      | Some info ->
          Error
            ("wrapped multi-module library interface " ^ info.name
           ^ " cannot be imported safely")
      | None ->
          let selected = dedup selected in
          let* _ =
            List.fold_result selected
              ~init:(Set.empty (module String))
              ~f:(fun names interface ->
                let name =
                  String.capitalize
                    Stdlib.Filename.(remove_extension (basename interface))
                in
                if Set.mem names name then
                  Error ("several Dune interfaces export module " ^ name)
                else Ok (Set.add names name))
          in
          Ok selected
      end
  | _ -> Error "source belongs to multiple Dune stanzas"

let config_paths ~root ~file =
  let rec config_files dir acc =
    let acc =
      List.map
        [ "dune"; "dune-project"; "dune-workspace"; "dune-workspace.dev" ]
        ~f:(Stdlib.Filename.concat dir)
      @ acc
    in
    if path_equal dir root then acc
    else
      let parent = Stdlib.Filename.dirname dir in
      if String.equal parent dir then acc else config_files parent acc
  in
  dedup (config_files (Stdlib.Filename.dirname file) [])

let find_root file =
  let rec walk dir project =
    if Stdlib.Sys.file_exists (Stdlib.Filename.concat dir "dune-workspace") then Some dir
    else
      let project =
        match project with
        | Some _ -> project
        | None ->
            Option.some_if
              (Stdlib.Sys.file_exists (Stdlib.Filename.concat dir "dune-project"))
              dir
      in
      let parent = Stdlib.Filename.dirname dir in
      if String.equal parent dir then project else walk parent project
  in
  walk (Stdlib.Filename.dirname file) None

let project_build_dir ~root =
  match Stdlib.Sys.getenv_opt "DUNE_BUILD_DIR" with
  | Some path when not (String.is_empty path) -> absolute ~root path
  | _ -> Stdlib.Filename.concat root "_build"

let source_for_build_path ~root ~build_directory path =
  match relative_to ~root:build_directory path with
  | Some relative ->
      begin match String.lsplit2 relative ~on:Stdlib.Filename.dir_sep.[0] with
      | Some (_, source) -> Stdlib.Filename.concat root source
      | None -> path
      end
  | None -> path

let inside_build ~root file =
  let build_dir = project_build_dir ~root in
  let inside dir = Option.is_some (relative_to ~root:dir file) in
  inside build_dir
  || List.exists
       (String.split file ~on:Stdlib.Filename.dir_sep.[0])
       ~f:(String.equal ".sandbox")

let dune_execution_path file =
  let path = String.map file ~f:(fun c -> if Char.equal c '\\' then '/' else c) in
  List.exists (String.split path ~on:'/') ~f:(fun component ->
      let component =
        if Stdlib.Sys.win32 then Stdlib.String.lowercase_ascii component else component
      in
      String.equal component "_build" || String.equal component ".sandbox")

let executable () =
  let separator = if Stdlib.Sys.win32 then ';' else ':' in
  let suffix = if Stdlib.Sys.win32 then ".exe" else "" in
  Option.bind (Stdlib.Sys.getenv_opt "PATH") ~f:(fun path ->
      String.split path ~on:separator
      |> List.find_map ~f:(fun dir ->
          let candidate = Stdlib.Filename.concat dir ("dune" ^ suffix) in
          Option.some_if (Stdlib.Sys.file_exists candidate) candidate))

let read_file path =
  let channel = Stdlib.open_in_bin path in
  Stdlib.Fun.protect
    ~finally:(fun () -> Stdlib.close_in channel)
    (fun () ->
      let length = Stdlib.in_channel_length channel in
      if length > 16_000_000 then Error "Dune description is too large"
      else Ok (Stdlib.really_input_string channel length))

let rec remove_tree path =
  match (Unix.lstat path).Unix.st_kind with
  | Unix.S_DIR ->
      Stdlib.Array.iter
        (fun name -> remove_tree (Stdlib.Filename.concat path name))
        (Stdlib.Sys.readdir path);
      Unix.rmdir path
  | Unix.S_REG | Unix.S_CHR | Unix.S_BLK | Unix.S_LNK | Unix.S_FIFO | Unix.S_SOCK ->
      Unix.unlink path

let describe ~root executable =
  let query_dir = Stdlib.Filename.temp_dir ~perms:0o700 "caravan-dune-" "" in
  Stdlib.Fun.protect
    ~finally:(fun () -> remove_tree query_dir)
    (fun () ->
      let stdout_path = Stdlib.Filename.concat query_dir "stdout" in
      let stderr_path = Stdlib.Filename.concat query_dir "stderr" in
      let build_dir = Stdlib.Filename.concat query_dir "build" in
      let args =
        [|
          executable;
          "describe";
          "workspace";
          "--root";
          root;
          "--build-dir";
          build_dir;
          "--format=csexp";
          "--lang=0.1";
        |]
      in
      let stdout =
        Unix.openfile stdout_path [ Unix.O_WRONLY; Unix.O_TRUNC; Unix.O_CREAT ] 0o600
      in
      let pid =
        Stdlib.Fun.protect
          ~finally:(fun () -> Unix.close stdout)
          (fun () ->
            let stderr =
              Unix.openfile stderr_path
                [ Unix.O_WRONLY; Unix.O_TRUNC; Unix.O_CREAT ]
                0o600
            in
            Stdlib.Fun.protect
              ~finally:(fun () -> Unix.close stderr)
              (fun () ->
                let null_device = if Stdlib.Sys.win32 then "NUL" else "/dev/null" in
                let input = Unix.openfile null_device [ Unix.O_RDONLY ] 0 in
                Stdlib.Fun.protect
                  ~finally:(fun () -> Unix.close input)
                  (fun () -> Unix.create_process executable args input stdout stderr)))
      in
      let deadline = Unix.gettimeofday () +. 10.0 in
      let output_too_large () =
        (Unix.stat stdout_path).Unix.st_size > 16_000_000
        || (Unix.stat stderr_path).Unix.st_size > 16_000_000
      in
      let rec await () =
        match Unix.waitpid [ Unix.WNOHANG ] pid with
        | 0, _ when output_too_large () ->
            Unix.kill pid Stdlib.Sys.sigkill;
            ignore (Unix.waitpid [] pid);
            Error "Dune metadata query produced too much output"
        | 0, _ when Float.(Unix.gettimeofday () >= deadline) ->
            Unix.kill pid Stdlib.Sys.sigkill;
            ignore (Unix.waitpid [] pid);
            Error "Dune metadata query timed out"
        | 0, _ ->
            ignore (Unix.select [] [] [] 0.05);
            await ()
        | _, Unix.WEXITED 0 -> read_file stdout_path
        | _, _ ->
            let* stderr = read_file stderr_path in
            Error ("Dune metadata query failed: " ^ String.strip stderr)
      in
      await ())

let resolve ~file : (t, Report.error) Result.t =
  let file =
    if Stdlib.Filename.is_relative file then
      Stdlib.Filename.concat (Stdlib.Sys.getcwd ()) file
    else file
  in
  if dune_execution_path file then Ok empty
  else
    let file = Unix.realpath file in
    match find_root file with
    | None -> Ok empty
    | Some root when inside_build ~root file -> Ok empty
    | Some root ->
        begin match executable () with
        | None -> Ok empty
        | Some executable ->
            let config_file =
              let workspace = Stdlib.Filename.concat root "dune-workspace" in
              if Stdlib.Sys.file_exists workspace then workspace
              else Stdlib.Filename.concat root "dune-project"
            in
            let report message =
              Report.error Type
                (Location.in_file config_file)
                ("Dune project discovery: " ^ message ^ " (use --no-dune to disable it)")
            in
            let* text = Result.map_error (describe ~root executable) ~f:report in
            let* sexp = Result.map_error (parse_csexp text) ~f:report in
            let* interfaces =
              Result.map_error
                (select ~build_directory:(project_build_dir ~root) ~root ~file sexp)
                ~f:report
            in
            let source_configs = config_paths ~root ~file in
            let interface_configs =
              List.concat_map interfaces ~f:(fun interface ->
                  let source =
                    source_for_build_path ~root ~build_directory:(project_build_dir ~root)
                      interface
                  in
                  if Option.is_some (relative_to ~root source) then
                    config_paths ~root ~file:source
                  else [])
            in
            let proof_candidates =
              List.map interfaces ~f:(fun interface ->
                  Stdlib.Filename.remove_extension interface ^ ".proof")
            in
            Ok
              {
                interfaces;
                dependencies =
                  dedup
                    (source_configs @ interface_configs @ interfaces @ proof_candidates);
              }
        end
