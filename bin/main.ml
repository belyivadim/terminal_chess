type color = White | Black
type piece_kind = Pawn | Knight | Bishop | Rook | Queen | King
type piece = { color : color; kind : piece_kind }
type cell = Empty | Occupied of piece
type board = cell array array
type vec2 = { x : int; y : int }
type move = { src : vec2; dest : vec2 }
(* type game_state = { board : board; turn : color; history : (move * board) list } *)
type castling_rights = { white : bool; wks : bool; wqs : bool; black : bool; bks : bool; bqs : bool }
type game_state = { board : board; turn : color; highlights : vec2 list; castling_rights : castling_rights }

let ansi_reset = "\027[0m"
let ansi_fg_white = "\027[97m"
let ansi_fg_black = "\027[30m"

let ansi_bg_white = "\027[47m"
let ansi_bg_black = "\027[100m"
let ansi_bg_highlight = "\027[42m"

let read_file filename =
  let ic = open_in filename in
  let len = in_channel_length ic in
  let content = really_input_string ic len in
  close_in ic;
  content

let color_to_string = function White -> "White" | Black -> "Black"
let toggle_color = function White -> Black | Black -> White

let in_bounds { x; y } = 
  x >= 0 && x < 8 && y >= 0 && y < 8

let get_cell (board : board) { x; y } = 
  if in_bounds { x; y } then board.(y).(x)
  else Empty

let piece_at board pos =
  match get_cell board pos with
  | Occupied p -> Some p
  | Empty -> None

let is_empty board pos = 
  match get_cell board pos with Empty -> true | _ -> false

let is_enemy board pos color =
  match get_cell board pos with
  | Occupied p when p.color <> color -> true
  | _ -> false

let pawn_moves board color pos =
  let dir = if color = White then -1 else 1 in
  let one_step = { x = pos.x; y = pos.y + dir } in
  let two_steps = { x = pos.x; y = pos.y + 2 * dir } in
  let diag_left = { x = pos.x - 1; y = pos.y + dir } in
  let diag_right = { x = pos.x + 1; y = pos.y + dir } in

  let forward_moves = 
    if is_empty board one_step then
      if (color = White && pos.y = 6) || (color = Black && pos.y = 1) then
        if is_empty board two_steps then [one_step; two_steps]
        else [one_step]
      else [one_step]
    else []
  in

  let capture_moves = 
    [diag_left; diag_right]
    |> List.filter (fun target -> is_enemy board target color)
  in

  forward_moves @ capture_moves

let knight_moves board color pos =
  let deltas = [
    (1, 2); (2, 1); (-1, 2); (-2, 1);
    (1, -2); (2, -1); (-1, -2); (-2, -1)
  ] in
  deltas
  |> List.map (fun (dx, dy) -> { x = pos.x + dx; y = pos.y + dy })
  |> List.filter (fun target ->
        match get_cell board target with
        | Empty -> true
        | Occupied p -> p.color <> color)

let collect_moves_by_directions directions board color pos = 
  let rec collect_dir (dx, dy) (x, y) acc =
    let nx = x + dx
    and ny = y + dy in
    if nx < 0 || nx > 7 || ny < 0 || ny > 7 then List.rev acc
    else
      match board.(ny).(nx) with
      | Empty -> collect_dir (dx, dy) (nx, ny) ({ x = nx; y = ny } :: acc)
      | Occupied p when p.color <> color ->
          List.rev ({ x = nx; y = ny } :: acc)
      | Occupied _ -> List.rev acc
  in

  directions
  |> List.map (fun dir -> collect_dir dir (pos.x, pos.y) [])
  |> List.flatten

let bishop_moves board color pos = 
  let directions = [ (1, 1); (-1, 1); (-1, -1); (1, -1) ] in
  collect_moves_by_directions directions board color pos

let rook_moves board color pos = 
  let directions = [ (1, 0); (0, 1); (-1, 0); (0, -1) ] in
  collect_moves_by_directions directions board color pos

let queen_moves board color pos =
  let directions = [ (1, 0); (0, 1); (-1, 0); (0, -1); (1, 1); (-1, 1); (-1, -1); (1, -1) ] in
  collect_moves_by_directions directions board color pos

let get_all_possible_check_moves board color = 
  let all_moves = ref [] in
  for y = 0 to 7 do
    for x = 0 to 7 do
      match board.(y).(x) with
      | Occupied p when p.color = color ->
          let pos = { x; y } in
          let moves =
            match p.kind with
            | Pawn -> pawn_moves board color pos
            | Knight -> knight_moves board color pos
            | Bishop -> bishop_moves board color pos
            | Rook -> rook_moves board color pos
            | King -> [] (* King cannot do check *)
            | Queen -> queen_moves board color pos
          in
          all_moves := moves @ !all_moves
      | _ -> ()
    done
  done;
  !all_moves

let is_attacked board pos op_color = 
  let moves = get_all_possible_check_moves board op_color in
  List.exists (fun m -> m = pos) moves

let king_moves board color pos castling_rights is_in_check = 
  let possible_moves_regular = [
    { x = pos.x - 1; y = pos.y - 1};
    { x = pos.x    ; y = pos.y - 1};
    { x = pos.x + 1; y = pos.y - 1};
    { x = pos.x - 1; y = pos.y    };
    { x = pos.x + 1; y = pos.y    };
    { x = pos.x - 1; y = pos.y + 1};
    { x = pos.x    ; y = pos.y + 1};
    { x = pos.x + 1; y = pos.y + 1};
  ] in
  let regular_moves 
    = possible_moves_regular |> List.filter (fun pos -> is_empty board pos || is_enemy board pos color) in

  let castling_moves =
    match color with
    | White ->
        let can_ks = 
          castling_rights.white &&
          castling_rights.wks &&
          not is_in_check &&
          board.(7).(5) = Empty &&
          board.(7).(6) = Empty &&
          not (is_attacked board { x = 5; y = 7 } Black) &&
          not (is_attacked board { x = 6; y = 7 } Black)
        in
        let can_qs = 
          castling_rights.white &&
          castling_rights.wqs &&
          not is_in_check &&
          board.(7).(1) = Empty &&
          board.(7).(2) = Empty &&
          board.(7).(3) = Empty &&
          not (is_attacked board { x = 2; y = 7 } Black) &&
          not (is_attacked board { x = 3; y = 7 } Black)
        in
        let cs = [] in
        let cs = if can_ks then { x = 6; y = 7 } :: cs else cs in
        let cs = if can_qs then { x = 2; y = 7 } :: cs else cs in
        cs

    | Black ->
        let can_ks = 
          castling_rights.black &&
          castling_rights.bks &&
          not is_in_check &&
          board.(0).(5) = Empty &&
          board.(0).(6) = Empty &&
          not (is_attacked board { x = 5; y = 0 } White) &&
          not (is_attacked board { x = 6; y = 0 } White)
        in
        let can_qs = 
          castling_rights.black &&
          castling_rights.bqs &&
          not is_in_check &&
          board.(0).(1) = Empty &&
          board.(0).(2) = Empty &&
          board.(0).(3) = Empty &&
          not (is_attacked board { x = 2; y = 0 } White) &&
          not (is_attacked board { x = 3; y = 0 } White)
        in
        let cs = [] in
        let cs = if can_ks then { x = 6; y = 0 } :: cs else cs in
        let cs = if can_qs then { x = 2; y = 0 } :: cs else cs in
        cs

  in
  regular_moves @ castling_moves

let legal_moves state pos = 
  let board = state.board in
  match piece_at board pos with
  | None -> []
  | Some { color; kind } ->
    let raw_moves = match kind with
      | Pawn -> pawn_moves board color pos
      | Knight -> knight_moves board color pos
      | Bishop -> bishop_moves board color pos
      | Rook -> rook_moves board color pos
      | Queen -> queen_moves board color pos
      | King -> 
          king_moves board color pos state.castling_rights (is_attacked board pos (toggle_color color))
          |> List.filter (fun m -> not (is_attacked state.board m (toggle_color color)))
    in
    List.filter in_bounds raw_moves

let is_legal_move (state : game_state) (move : move) : bool =
  match piece_at state.board move.src with
  | Some { color; _ } when color = state.turn ->
    legal_moves state move.src
    |> List.exists (fun pos -> pos = move.dest)
  | _ -> false

let default_board () : board = 
  let empty_row = Array.init 8 (fun _ -> Empty) in
  let mk_piece color kind = Occupied { color; kind } in
  let back_rank color =
    [ Rook; Knight; Bishop; Queen; King; Bishop; Knight; Rook ]
    |> List.map (mk_piece color)
    |> Array.of_list
  in
  let pawn_row color = Array.init 8 (fun _ -> mk_piece color Pawn) in
  Array.init 8 (function
      | 0 -> back_rank Black
      | 1 -> pawn_row Black
      | 6 -> pawn_row White
      | 7 -> back_rank White
      | _ -> Array.copy empty_row
    )



let piece_to_string (p : piece) : string = 
  match p.kind with
  | King -> "♔"
  | Queen -> "♕"
  | Rook -> "♖"
  | Bishop -> "♗"
  | Knight -> "♘"
  | Pawn -> "♙"

let cell_color x y is_highlighed =
  if is_highlighed then ansi_bg_highlight
  else if (x + y) mod 2 = 0 
  then ansi_bg_white 
  else ansi_bg_black

let cell_to_string (x, y) is_highlighted = function
  | Empty -> 
      let bg = cell_color x y is_highlighted in
      bg ^ "   " ^ ansi_reset
  | Occupied p -> 
    let bg = cell_color x y is_highlighted in
    let fg = if p.color = White then ansi_fg_white else ansi_fg_black in
    let piece = piece_to_string p in
    bg ^ fg ^ " " ^ piece ^ " " ^ ansi_reset

let print_board (board : board) (highlights : vec2 list) : unit = 
  let is_highlighted x y =
    List.exists (fun v -> v.x = x && v.y = y) highlights
  in
  for y = 0 to 7 do
    let rank = 8 - y in
    Printf.printf "%d " rank;
    for x = 0 to 7 do
      let cell = board.(y).(x) in
      Printf.printf "%s" (cell_to_string (x, y) (is_highlighted x y) cell)
    done;
    print_newline ()
  done;
  print_endline "   a  b  c  d  e  f  g  h" 

let apply_move (board : board) (mv : move) : board = 
  let src = mv.src
  and dest = mv.dest in
  match board.(src.y).(src.x) with
  | Empty -> board
  | Occupied p ->
      Array.mapi (fun y row ->
        Array.mapi (fun x cell ->
          if x = src.x && y = src.y then Empty
          else if x = dest.x && y = dest.y then Occupied p
          else cell
        ) row
      ) board

let put_piece board piece pos = 
  Array.mapi (fun y row ->
    Array.mapi (fun x cell ->
      if x = pos.x && y = pos.y then Occupied piece
      else cell
    ) row
  ) board


let castling board p mv = 
  if p.kind = King && p.color = White && mv.src = { x = 4; y = 7 } && mv.dest = { x = 6; y = 7 } then begin
    (* white kingside *)
    let mv2 = { src = { x = 7; y = 7 }; dest = { x = 5; y = 7} } in
    apply_move board mv2
  end else if p.kind = King && p.color = White && mv.src = { x = 4; y = 7 } && mv.dest = { x = 2; y = 7 } then begin
    (* white queenside *)
    let mv2 = { src = { x = 0; y = 7 }; dest = { x = 3; y = 7 } } in
    apply_move board mv2
  end else if p.kind = King && p.color = Black && mv.src = { x = 4; y = 0 } && mv.dest = { x = 6; y = 0 } then begin
    (* black kingside *)
    let mv2 = { src = { x = 7; y = 0 }; dest = { x = 5; y = 0} } in
    apply_move board mv2
  end else if p.kind = King && p.color = Black && mv.src = { x = 4; y = 0 } && mv.dest = { x = 2; y = 0 } then begin
    (* black queenside *)
    let mv2 = { src = { x = 0; y = 0 }; dest = { x = 3; y = 0 } } in
    apply_move board mv2
  end else 
    (* Regular move, no castling *)
    board

let transform_piece state mv = function
  | None -> Ok state.board
  | Some piece_kind ->
    if state.turn = White && mv.dest.y = 0 && state.board.(mv.dest.y).(mv.dest.x) = Occupied { color = White; kind = Pawn } ||
        state.turn = Black && mv.dest.y = 7 && state.board.(mv.dest.y).(mv.dest.x) = Occupied { color = Black; kind = Pawn } then
      Ok (put_piece state.board { color = state.turn; kind = piece_kind } mv.dest)
    else
      Error "Illegal attemt to transform a piece"

let try_move (state : game_state) (mv : move) (wanted_piece_kind : piece_kind option) : (game_state, string) result =
  let { board; turn; _; } = state in
  if is_legal_move state mv then
    match board.(mv.src.y).(mv.src.x) with
    | Empty -> Error "No piece at source position"
    | Occupied p ->
      if p.color <> turn then
        Error "That is not your piece"
      else begin
        let new_board = apply_move board mv in
        let new_board = castling new_board p mv in
        match transform_piece { state with board = new_board } mv wanted_piece_kind with
        | Error msg -> Error msg
        | Ok new_board -> Ok { state with board = new_board }
      end
  else
    Error "The move is not legal."

let pos_of_notation s =
  if String.length s <> 2 then None
  else
    let file = s.[0]
    and rank = s.[1] in
    if file >= 'a' && file <= 'h' && rank >= '1' && rank <= '8' then
      let x = Char.code file - Char.code 'a' in
      let y = 7 - (Char.code rank - Char.code '1') in
      Some { x; y; }
    else None

let notation_of_pos (pos : vec2) : string = 
  (Char.code 'a' + pos.x |> char_of_int |> String.make 1) ^ (8 - pos.y |> string_of_int)


let find_kings (board : board) : (vec2 option * vec2 option) = 
  let white = ref None
  and black = ref None in
  for y = 0 to 7 do
    for x = 0 to 7 do
      match board.(y).(x) with
      | Occupied { color = White; kind = King } -> white := Some { x; y }
      | Occupied { color = Black; kind = King } -> black := Some { x; y }
      | _ -> ()
    done
  done;
  (!white, !black)

let is_check (board : board) : bool * bool = 
  let w_king_pos_opt, b_king_pos_opt = find_kings board in
  let white = match w_king_pos_opt with
  | None -> false
  | Some pos -> is_attacked board pos Black in
  let black = match b_king_pos_opt with
  | None -> false
  | Some pos -> is_attacked board pos White in
  (white, black)

let piece_of_string str =
  match String.lowercase_ascii str with
  | "p" | "pawn" -> Some Pawn
  | "r" | "rook" -> Some Rook
  | "n" | "knight" -> Some Knight
  | "b" | "bishop" -> Some Bishop
  | "q" | "queen" -> Some Queen
  | "k" | "king" -> Some King
  | _ -> None

let cell_of_string str =
  match String.lowercase_ascii str with
  | "e" -> Empty
  | symbol when String.length symbol = 1 && 
    'a' <= symbol.[0] && symbol.[0] <= 'z' -> (
      let color_of_char c = if 'A' <= c && c <= 'Z' then White else Black in
      match piece_of_string symbol with
      | None -> failwith ("Could not parse piece `" ^ symbol ^ "`")
      | Some piece_kind -> Occupied { color = color_of_char str.[0]; kind = piece_kind }
    )
  | _ -> failwith "Could not parse cell."

let rec split_n n lst =
  if n = 0 then ([], lst)
  else match lst with
    | [] -> ([], [])
    | x :: xs ->
      let (left, right) = split_n (n - 1) xs in
      (x :: left, right)

let parse_board (input : string) = 
  let tokens = input |> String.split_on_char ',' |> List.map String.trim |> List.filter (fun s -> s <> "") in
  if List.length tokens <> 64 then failwith "Invalid board layout, must contain 64 cells"
  else
    let rec to_rows tokens acc =
      match tokens with
      | [] -> List.rev acc
      | _ ->
        let row, rest = split_n 8 tokens in
        to_rows rest (Array.of_list (List.map cell_of_string row) :: acc)
    in
    Array.of_list (to_rows tokens [])

let parse_command (input : string) : [`Moves of vec2 | `Move of (move * piece_kind option) | `Invalid of string] =
  match String.split_on_char ' ' input with
  | ["moves"; pos_not] -> (
      match pos_of_notation  pos_not with
      | None -> `Invalid "Invalid coordinates for 'moves'"
      | Some pos -> `Moves pos
    )
  | [pos_not1; ">"; pos_not2] 
  | ["move"; pos_not1; ">"; pos_not2] -> (
      match pos_of_notation pos_not1, pos_of_notation pos_not2 with
      | Some src, Some dest -> `Move ({ src; dest; }, None)
      | _ -> `Invalid "Invalid coordinates for 'move'"
    )
  | [pos_not1; ">"; pos_not2; ">"; wanted_piece]
  | ["move"; pos_not1; ">"; pos_not2; ">"; wanted_piece] -> (
      match pos_of_notation pos_not1, pos_of_notation pos_not2, piece_of_string wanted_piece with
      | Some src, Some dest, Some piece -> 
          if piece = King then
            `Invalid "Cannot transform pawn into King"
          else 
            `Move ({ src; dest; }, Some piece)
      | _ -> `Invalid "Invalid coordinates for 'move' or invalid piece"
    )
  | _ -> `Invalid "Unrecognized command"

let update_castling_rights rights = function
  | { x = 0; y = 7 } -> { rights with wqs = false }
  | { x = 7; y = 7 } -> { rights with wks = false }
  | { x = 4; y = 7 } -> { rights with white = false }
  | { x = 0; y = 0 } -> { rights with bqs = false }
  | { x = 7; y = 0 } -> { rights with bks = false }
  | { x = 4; y = 0 } -> { rights with black = false }
  | _ -> rights

let init_board () : board = 
  if Array.length Sys.argv >= 2 then begin
    let layout_txt = read_file Sys.argv.(1) in
    try
    parse_board layout_txt
    with
    | Failure msg -> (
      Printf.printf "Error during parsing the board: %s\n" msg;
      Printf.printf "Loading default board.\n";
      default_board ()
    )
  end else default_board ()

(* Initialization and loop *)
let rec game_loop (state : game_state) = 
  print_board state.board state.highlights;
  Printf.printf "%s > " (color_to_string state.turn);
  flush stdout;
  match read_line () with
  | exception End_of_file -> ()
  | line -> (
    match parse_command line with
    | `Moves pos ->
        let moves = legal_moves state pos in
        Printf.printf "Legal moves for %s: "  (notation_of_pos pos);
        List.iter (fun m -> Printf.printf "%s " (notation_of_pos m)) moves;
        print_newline ();
        game_loop { state with highlights = moves };
    | `Move mv -> (
        let (mv, wanted_piece_kind) = mv in
        match try_move state mv wanted_piece_kind with
        | Ok new_state ->
            let white_check, black_check = is_check new_state.board in
            if white_check && state.turn = White || black_check && state.turn = Black then begin
              Printf.printf "This move will expose your King. Try another one.\n";
              game_loop state
            end else begin
              let white_check, black_check = is_check new_state.board in
              if black_check && state.turn = White || white_check && state.turn = Black then
                Printf.printf "%s King is checked!\n" (color_to_string (toggle_color state.turn));
              let new_state = { 
                board = new_state.board;
                turn = toggle_color state.turn; 
                highlights = [];
                castling_rights = update_castling_rights state.castling_rights mv.src }
              in
              game_loop new_state
            end
        | Error msg ->
          Printf.printf "Error: %s\n" msg;
          game_loop state
      )
    | `Invalid msg ->
        Printf.printf "Error: %s\n" msg;
        game_loop state
    )

let () =
  let initial_state = {
    board = init_board ();
    turn = White;
    highlights = [];
    castling_rights = { white = true; wks = true; wqs = true; black = true; bks = true; bqs = true };
  } in
  game_loop initial_state
