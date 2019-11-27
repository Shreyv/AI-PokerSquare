
import java.util.Collections;
import java.util.Stack;

/**
 * FlushPlayer - a simple example implementation of the player interface for
 * PokerSquares that attempts to get flushes in the first four columns. Author:
 * ________, based on code provided by Todd W. Neller and Michael Fleming
 */
public class FlushPlayer implements PokerSquaresPlayer {

    private final int SIZE = 5; // number of rows/columns in square grid
    private final int NUM_POS = SIZE * SIZE; // number of positions in square grid
    private final int NUM_CARDS = Card.NUM_CARDS; // number of cards in deck
    private Card[][] grid = new Card[SIZE][SIZE]; // grid with Card objects or null (for empty positions)

    /* (non-Javadoc)
	 * @see PokerSquaresPlayer#setPointSystem(PokerSquaresPointSystem, long)
     */
    @Override
    public void setPointSystem(PokerSquaresPointSystem system, long millis) {
        // The FlushPlayer, like the RandomPlayer, does not worry about the scoring system.	
    }

    /* (non-Javadoc)
	 * @see PokerSquaresPlayer#init()
     */
    @Override
    public void init() {
        // clear grid
        for (int row = 0; row < SIZE; row++) {
            for (int col = 0; col < SIZE; col++) {
                grid[row][col] = null;
            }
        }

    }

    /* (non-Javadoc)
	 * @see PokerSquaresPlayer#getPlay(Card, long)
     */
    @Override
    public int[] getPlay(Card card, long millisRemaining) {
        int cardrow = 0;
       

        int cardrank = card.getRank();
        int cardsuit = card.getSuit();

        int cardcol = cardsuit;
        
        if(grid[SIZE-1][cardcol] != null && grid[SIZE-1][SIZE-1] == null){
                cardcol = 4;
        }
        else if (grid[SIZE-1][SIZE-1] != null && grid[SIZE-1][cardcol] != null){
                cardcol = grid[SIZE-1][0] == null ? 0 : (grid[SIZE-1][1] == null ? 1 : (grid[SIZE-1][2] == null ? 2 : 3)); 
        }
        
        while (grid[cardrow][cardcol] != null && cardrow < SIZE){
            cardrow++;
        }
        
        grid[cardrow][cardcol] = card;

        int[] playPos = {cardrow, cardcol};
        return playPos;
    }

    /* (non-Javadoc)
	 * @see PokerSquaresPlayer#getName()
     */
    @Override
    public String getName() {
        return "FlushPlayer";
    }

    /**
     * Demonstrate FlushPlayer play with British point system.
     *
     * @param args (not used)
     */
    public static void main(String[] args) {
        PokerSquaresPointSystem system = PokerSquaresPointSystem.getBritishPointSystem();
        System.out.println(system);
        new PokerSquares(new FlushPlayer(), system).play(); // play a single game
    }

}
