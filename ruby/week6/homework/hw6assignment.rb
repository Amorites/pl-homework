# University of Washington, Programming Languages, Homework 6, hw6runner.rb

# This is the only file you turn in, so do not modify the other files as
# part of your solution.

class MyPiece < Piece
  # The constant All_My_Pieces should be declared here
  # All_My_Pieces = All_Pieces + [
  All_My_Pieces = [
    rotations([[0, 0], [-1, 0], [-1, -1], [1, 0], [0, -1]]),
    [[[0, 0], [-1, 0], [1, 0], [2, 0], [3, 0]], 
    [[0, 0], [0, -1], [0, 1], [0, 2], [0, 3]]],
    rotations([[0, 0], [1, 0], [0, 1]])
  ]

  # your enhancements here
  # class method to choose the next piece
  def self.next_piece (board)
    MyPiece.new(All_My_Pieces.sample, board)
  end
end

class MyBoard < Board
  # your enhancements here
  def initialize (game)
    @grid = Array.new(num_rows) {Array.new(num_columns)}
    @current_block = MyPiece.next_piece(self)
    @score = 0
    @game = game
    @delay = 500
  end

  def rotate_reversion
    if !game_over? and @game.is_running?
      @current_block.move(0, 0, 2)
    end
    draw
  end

  def next_piece
    @current_block = MyPiece.next_piece(self)
    @current_pos = nil
  end

  # maybe modify on origin class is better?
  def store_current
    locations = @current_block.current_rotation
    displacement = @current_block.position
    (0..@current_pos.size - 1).each{|index| 
      current = locations[index];
      @grid[current[1]+displacement[1]][current[0]+displacement[0]] = 
      @current_pos[index]
    }
    remove_filled
    @delay = [@delay - 2, 80].max
  end

end

class MyTetris < Tetris
  # your enhancements here
  def set_board
    @canvas = TetrisCanvas.new
    @board = MyBoard.new(self)
    @canvas.place(@board.block_size * @board.num_rows + 3,
                  @board.block_size * @board.num_columns + 6, 24, 80)
    @board.draw
  end


  def key_bindings  
    super
    @root.bind('u', proc {@board.rotate_reversion})
  end

end


