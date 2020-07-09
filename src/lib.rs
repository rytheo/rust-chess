use regex::Regex;
use std::cmp::{Eq, PartialEq};
use std::convert::TryFrom;
use std::{fmt, ops};
use std::io::{stdin, stdout, Write};
use termion::{clear, color, cursor};

use PieceType::{King, Queen, Rook, Bishop, Knight, Pawn};
use PieceColor::{White, Black};


/// A chess game.
///
/// Stores the current board state and move history.
pub struct Game {
    board: [[Option<Piece>; 8]; 8],
    moves: Vec<Move>,
}

impl Game {
    /// Constructs a new `Game`.
    ///
    /// Initializes the board with all pieces in their starting positions.
    pub fn new() -> Game {
        let back_rank = [Rook, Knight, Bishop, Queen, King, Bishop, Knight, Rook];
        let mut board = [[None; 8]; 8];
        for (y1, y2, color) in &[(0, 1, White), (7, 6, Black)] {
            for (x, ptype) in back_rank.iter().enumerate() {
                board[*y1][x] = Some(Piece(*ptype, *color));
            }
            board[*y2] = [Some(Piece(Pawn, *color)); 8];
        }
        Game { board, moves: vec![] }
    }

    /// Runs the main game loop.
    ///
    /// Prompts the active player for a move, executes it if legal, then
    /// repeats until checkmate or stalemate is reached.
    pub fn run(&mut self) {
        self.draw_board();
        println!();
        loop {
            let color = self.active_color();
            // Compute possible moves
            let moves = self.possible_moves(color, true);
            // Test for checkmate or stalemate
            if moves.len() == 0 {
                let mut checkmate = false;
                for enemy_move in self.possible_moves(!color, false) {
                    if let Move::Normal { taken, .. } = enemy_move {
                        if let Some(Piece(King, ..)) = taken {
                            checkmate = true;
                            break;
                        }
                    }
                }
                if checkmate {
                    println!("Checkmate - {:?} wins", !color);
                } else {
                    println!("Stalemate - Draw");
                }
                break;
            }
            // Prompt the user for a move
            print!("[{:?}]> ", color);
            stdout().flush().unwrap();
            let mut input = String::new();
            stdin().read_line(&mut input).unwrap();
            // Process the input and print any errors
            let res = self.eval(&input, moves);
            self.draw_board();
            match res {
                Ok(_) => println!(),
                Err(msg) => println!("Error: {}", msg),
            }
        }
    }

    /// Parses and evaluates `input` using algebraic chess notation.
    ///
    /// If there is exactly one match in `moves`, that `Move` is returned.
    /// Otherwise, returns an error message.
    fn eval(&mut self, input: &str, moves: Vec<Move>) -> Result<Move, String> {
        let re = Regex::new(r"(?x)
            \b([KQRBN]?)([a-h])?([1-8])?([a-h])([1-8])([QRBN])?\b # normal move
            |
            \b(0-0(-0)?)\b # castle
        ").unwrap();
        let caps = re.captures(input).ok_or(String::from("Invalid syntax"))?;
        let pcolor = self.active_color();
        // Normal move
        if caps.get(1).is_some() {
            let ptype = PieceType::try_from(&caps[1]).unwrap();
            let x1 = caps.get(2).map(|m| file_to_int(m.as_str()).unwrap());
            let y1 = caps.get(3).map(|m| m.as_str().parse::<usize>().unwrap() - 1);
            let x2 = file_to_int(&caps[4]).unwrap();
            let y2 = caps[5].parse::<usize>().map(|n| n - 1).unwrap();
            let prom = match caps.get(6) {
                Some(mat) => PieceType::try_from(mat.as_str()).ok(),
                None => None,
            };
            let mut candidate = None;
            for mov in moves {
                let (pt, start, end) = match mov {
                    Move::Normal { piece, start, end, ..} => (piece.0, start, end),
                    Move::EnPassant { start, end, ..} => (Pawn, start, end),
                    Move::Castle { .. } => continue,
                };
                if pt == ptype && (x2, y2) == end && (x1.unwrap_or(start.0), y1.unwrap_or(start.1)) == start {
                    if candidate.is_none() {
                        candidate = Some(mov);
                    } else {
                        return Err(String::from("Ambiguous move"));
                    }
                }
            }
            // In case of pawn promotion
            if let Some(mov) = candidate {
                self.apply(mov);
                if let Move::Normal { piece: Piece(Pawn, ..), end: (x, y), .. } = mov {
                    let end_rank = if pcolor == White { 7 } else { 0 };
                    if y == end_rank {
                        if let Some(pt) = prom {
                            self.board[y][x] = Some(Piece(pt, pcolor));
                        } else {
                            self.undo();
                            return Err(String::from("Must specify piece to replace promoted pawn"))
                        }
                    }
                }
            }
            candidate.ok_or(String::from("Illegal move"))
        // Castling
        } else {
            let qs = caps.get(8).is_some();
            for mov in moves {
                if let Move::Castle { queenside, .. } = mov {
                    if queenside == qs {
                        self.apply(mov);
                        return Ok(mov);
                    }
                }
            }
            Err(String::from("Cannot castle"))
        }
    }

    /// Checks some of the requirements for castling, ignoring safety.
    ///
    /// Returns a `Move` if possible, or an error message otherwise.
    fn castle(&mut self, queenside: bool) -> Result<Move, String> {
        let color = self.active_color();
        let rank = if color == White { 0 } else { 7 };
        let kx1 = 4;
        let rx1 = if queenside { 0 } else { 7 };
        // Search move history to see if King or Rook have moved
        for mov in &self.moves {
            match *mov {
                Move::Normal { start: (x, y), .. } => {
                    if y == rank {
                        if x == kx1 {
                            return Err(String::from("King has already moved"));
                        } else if x == rx1 {
                            return Err(String::from("Rook has already moved"));
                        }
                    }
                }
                Move::Castle { color: c, .. } if c == color => return Err(String::from("Player has already castled")),
                _ => ()
            }
        }
        // If squares are not empty
        let mut xrange = if queenside { 1..=3 } else { 5..=6 };
        if xrange.any(|x| self.board[rank][x].is_some()) {
            return Err(String::from("Occupied square between King and Rook"));
        }
        // Return valid castle
        Ok(Move::Castle { color, queenside })
    }

    /// Returns a `Vec` containing each `Move` that the `active_color` player can make.
    ///
    /// If `safe_only` is `true`, this function omits any `Move` that would
    /// leave the player's King in check.
    fn possible_moves(&mut self, active_color: PieceColor, safe_only: bool) -> Vec<Move> {
        let mut moves = vec![];
        for y in 0..8 {
            for x in 0..8 {
                if let Some(Piece(ptype, color)) = self.board[y][x] {
                    if color == active_color {
                        match ptype {
                            King | Queen | Rook | Bishop | Knight => {
                                for (dx, dy) in ptype.deltas() {
                                    let (mut x1, mut y1) = (x as i8 + dx, y as i8 + dy);
                                    while in_bounds(x1, y1) {
                                        let dest = self.board[y1 as usize][x1 as usize];
                                        if dest.is_some() && dest.unwrap().1 == active_color { break; }
                                        moves.push(Move::Normal {
                                            piece: Piece(ptype, color),
                                            start: (x, y),
                                            end: (x1 as usize, y1 as usize),
                                            taken: dest,
                                        });
                                        if dest.is_some() || ptype == King || ptype == Knight { break; }
                                        x1 += dx;
                                        y1 += dy;
                                    }
                                }
                            }
                            Pawn => {
                                let y_dir = if active_color == White { 1 } else { -1 };
                                // Take enemy piece
                                for dx in &[-1, 1] {
                                    let (x1, y1) = (x as i8 + dx, y as i8 + y_dir);
                                    if in_bounds(x1, y1) {
                                        // Diagonal to capture
                                        let dest = self.board[y1 as usize][x1 as usize];
                                        if dest.is_some() && dest.unwrap().1 != active_color {
                                            moves.push(Move::Normal {
                                                piece: Piece(ptype, color),
                                                start: (x, y),
                                                end: (x1 as usize, y1 as usize),
                                                taken: dest,
                                            })
                                        }
                                        // En passant
                                        if let Some(Move::Normal { piece, start, end, .. }) = self.moves.last() {
                                            let rank = if color == White { 6 } else { 1 };
                                            let x_diff = if start.0 > x { start.0 - x } else { x - start.0 };
                                            if piece.0 == Pawn && x_diff == 1 && start.1 == rank && end.1 == y {
                                                moves.push(Move::EnPassant {
                                                    color,
                                                    start: (x, y),
                                                    end: (x1 as usize, y1 as usize),
                                                })
                                            }
                                        }
                                    }
                                }
                                // Move forward
                                let rank = if color == White { 1 } else { 6 };
                                let dy_max = if y == rank { 2 } else { 1 };
                                for dy in 1..=dy_max {
                                    let y1 = y as i8 + dy*y_dir;
                                    if in_bounds(x as i8, y1) {
                                        if self.board[y1 as usize][x].is_some() {
                                            break;
                                        }
                                        moves.push(Move::Normal {
                                            piece: Piece(ptype, color),
                                            start: (x, y),
                                            end: (x, y1 as usize),
                                            taken: None,
                                        })
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        // Edge case: castling
        for side in &[true, false] {
            if let Ok(mov) = self.castle(*side) {
                moves.push(mov);
            }
        }
        if safe_only {
            let mut safe_moves = vec![];
            for mov in moves {
                self.apply(mov);
                let mut safe = true;
                for enemy_move in self.possible_moves(!active_color, false) {
                    if let Move::Normal { end: (x2, y2), taken, ..} = enemy_move {
                        if let Some(Piece(King, ..)) = taken {
                            safe = false;
                            break;
                        }
                        // Check if previous castle was legal
                        if let Move::Castle { color, queenside } = mov {
                            let y = if color == White { 0 } else { 7 };
                            let xrange = if queenside { 2..=4 } else { 4..=6 };
                            if y2 == y && xrange.contains(&x2) {
                                safe = false;
                                break;
                            }
                        }
                    }
                }
                self.undo();
                if safe {
                    safe_moves.push(mov);
                }
            }
            safe_moves
        } else {
            moves
        }
    }

    /// Applies a `Move` to the board and adds it to the move history.
    fn apply(&mut self, mov: Move) {
        match mov {
            Move::Normal { start: (x1, y1), end: (x2, y2), .. } => {
                self.board[y2][x2] = self.board[y1][x1].take();
            }
            Move::EnPassant { start: (x1, y1), end: (x2, y2), .. } => {
                self.board[y2][x2] = self.board[y1][x1].take();
                self.board[y1][x2] = None;
            }
            Move::Castle { color, queenside } => {
                let kx1 = 4;
                let y = if color == White { 0 } else { 7 };
                let (rx1, rx2, kx2) = if queenside { (0, 3, 2) } else { (7, 5, 6) };
                self.board[y][kx2] = self.board[y][kx1].take();
                self.board[y][rx2] = self.board[y][rx1].take();
            }
        }
        self.moves.push(mov);
    }

    /// Rewinds the game by one `Move` (if one has been made).
    fn undo(&mut self) {
        match self.moves.last() {
            Some(Move::Normal { start, end, taken, .. }) => {
                let (x1, y1) = *start;
                let (x2, y2) = *end;
                self.board[y1][x1] = self.board[y2][x2].take();
                self.board[y2][x2] = *taken;
            }
            Some(Move::EnPassant { color, start, end }) => {
                let (x1, y1) = *start;
                let (x2, y2) = *end;
                self.board[y1][x1] = self.board[y2][x2].take();
                self.board[y1][x2] = Some(Piece(Pawn, !*color));
            }
            Some(Move::Castle { color, queenside }) => {
                let kx1 = 4;
                let y = if *color == White { 0 } else { 7 };
                let (rx1, rx2, kx2) = if *queenside { (0, 3, 2) } else { (7, 5, 6) };
                self.board[y][kx1] = self.board[y][kx2].take();
                self.board[y][rx1] = self.board[y][rx2].take();
            }
            None => return,
        }
        self.moves.pop();
    }

    /// Clears the terminal, then draws the current board state.
    fn draw_board(&self) {
        print!("{}{}", clear::All, cursor::Goto(1, 1));
        for (y, row) in self.board.iter().enumerate().rev() {
            print!("{} ", y + 1); // Rank label
            for (x, space) in row.iter().enumerate() {
                // Determine the color of this square
                match (y + x) % 2 == 0 {
                    true => print!("{}", color::Bg(color::Reset)),
                    false => print!("{}", color::Bg(color::LightBlack)),
                };
                // Display a piece if it's on this square
                match space {
                    Some(piece) => print!("{} ", piece),
                    None => print!("  "),
                };
            }
            println!("{}", color::Bg(color::Reset));
        }
        println!("  a b c d e f g h \n"); // File labels
    }

    /// Returns the `PieceColor` of the active player.
    fn active_color(&self) -> PieceColor {
        if self.moves.len() % 2 == 0 { White } else { Black }
    }

}

/// A chess move.
///
/// Contains data for advancing or rewinding the board state.
#[derive(Copy, Clone, Debug)]
enum Move {
    Normal {
        piece: Piece,
        start: (usize, usize),
        end: (usize, usize),
        taken: Option<Piece>,
    },
    EnPassant {
        color: PieceColor,
        start: (usize, usize),
        end: (usize, usize),
    },
    Castle {
        color: PieceColor,
        queenside: bool,
    },
}

/// A chess piece represented as a `PieceType` and `PieceColor` pair.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Piece(PieceType, PieceColor);

impl fmt::Display for Piece {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let i = self.0 as usize + 6 * self.1 as usize;
        let symbol = "♔♕♖♗♘♙♚♛♜♝♞♟︎".chars().nth(i).unwrap();
        write!(f, "{}", symbol)
    }
}

/// One of six chess piece types.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PieceType {
    King,
    Queen,
    Rook,
    Bishop,
    Knight,
    Pawn,
}

impl PieceType {
    fn deltas(&self) -> Vec<(i8, i8)> {
        match self {
            King | Queen => vec![(-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 1)],
            Rook => vec![(-1, 0), (1, 0), (0, -1), (0, 1)],
            Bishop => vec![(-1, -1), (-1, 1), (1, -1), (1, 1)],
            Knight => vec![(-2, -1), (-2, 1), (-1, -2), (-1, 2), (1, -2), (1, 2), (2, -1), (2, 1)],
            Pawn => panic!("Not implemented for Pawn"),
        }
    }
}

impl TryFrom<&str> for PieceType {
    type Error = &'static str;
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        match s {
            "K" => Ok(King),
            "Q" => Ok(Queen),
            "R" => Ok(Rook),
            "B" => Ok(Bishop),
            "N" => Ok(Knight),
            "" => Ok(Pawn),
            _ => Err("String must be one of [KQRBN] or empty"),
        }
    }
}

/// One of two chess piece colors.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PieceColor {
    White,
    Black,
}

impl ops::Not for PieceColor {
    type Output = Self;
    fn not(self) -> Self::Output {
        match self {
            White => Black,
            Black => White,
        }
    }
}


/// Tries to convert a file character (a-h) to its corresponding x coordinate.
fn file_to_int(file: &str) -> Result<usize, ()> {
    let c = file.chars().next().ok_or(())?;
    for (i, letter) in "abcdefgh".chars().enumerate() {
        if c == letter {
            return Ok(i);
        }
    }
    Err(())
}

/// Returns `true` if `x` and `y` are both in `0..8`.
fn in_bounds(x: i8, y: i8) -> bool {
    0 <= x && x < 8 && 0 <= y && y < 8
}
