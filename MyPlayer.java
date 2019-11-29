
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Random;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

public class MyPlayer implements PokerSquaresPlayer {

    private final int SIZE = 5; // row or col size of the grid
    private final int NUM_POS = SIZE * SIZE; // grid size or number of positions available
    private Random random = new Random(); // random generator
    private int numPlays = 0; // cards placed in the grid
    private PokerSquaresPointSystem system;
    private Card[][] grid = new Card[SIZE][SIZE]; //  grid for placing cards
    private Card[] simDeck = Card.getAllCards(); // deck of all cards
    private int[] rankMap = new int[Card.NUM_RANKS]; // cards available for a particular rank
    private int[] suitMap = new int[Card.NUM_SUITS]; // cards available for a particular suit
    private List<Set<Integer>> straights = new LinkedList<>(); // pre computed all possible straights
    private final int DEPTH = 10; // Depth for MC simulations
    private final int PRIORITY_COUNT = 5; // number of elements to be selected from priority queue

    private Set<Integer> availablePositions = new HashSet<>(); // track of available positions

    @Override
    public void setPointSystem(PokerSquaresPointSystem system, long millis) {
        this.system = system;
    }

    @Override
    public void init() {
        simDeck = Card.getAllCards(); // initializing sim deck before starting new game
        // clearing grid
        for (int row = 0; row < SIZE; row++) {
            for (int col = 0; col < SIZE; col++) {
                grid[row][col] = null;
            }
        }
        // reset numPlays
        numPlays = 0;
        // (re)initialize available positions
        for (int i = 0; i < NUM_POS; i++) {
            availablePositions.add(i);
        }

        for (int i = 0; i < Card.NUM_RANKS; i++) {
            rankMap[i] = 4; // reseting every count of rank to 4
            if (i < Card.NUM_RANKS - 3) {
                Set<Integer> straight = new HashSet<>();
                // adding combination of the straight 10,J,Q,K,A
                if (i == 9) {
                    for (int j = i; j < i + 4; j++) {
                        straight.add(j);
                    }
                    straight.add(0);
                } else {
                    for (int j = i; j < i + 5; j++) {
                        straight.add(j); // adding all other straights
                    }
                }
                straights.add(straight);
            }
        }

        for (int i = 0; i < Card.NUM_SUITS; i++) {
            suitMap[i] = 13; // reseting every count of suit to 13
        }

    }

    /**
     * Returns the position of the card to be placed. It runs Greedy MC
     * simulations and returns the row and col position of the card to be
     * placed.
     *
     * @param card
     * @param millisRemaining
     * @return
     */
    @Override
    public int[] getPlay(Card card, long millisRemaining) {
        millisRemaining -= 1;
        long starttime = System.currentTimeMillis();
        int rowColPosition = 0, row = 0, col = 0, rowEmptyCount, colEmptyCount;
        rankMap[card.getRank()]--;
        suitMap[card.getSuit()]--;
        simDeck[card.getCardId()] = null;
        List<Integer> bestPlays = new ArrayList<>();

        switch (numPlays) {
            // random selection for first card
            case 0:
                rowColPosition = random.nextInt(NUM_POS);
                break;
            // forced placement for the last position     
            case NUM_POS - 1:
                rowColPosition = availablePositions.iterator().next();
                break;
            default:
                double maxPoints = Double.NEGATIVE_INFINITY;
                // Priority queue for adding postions
                PriorityQueue<Position> pq = new PriorityQueue(new PositionComparator());
                for (int pos : availablePositions) {
                    rowEmptyCount = 0;
                    colEmptyCount = 0;
                    row = pos / SIZE;
                    col = pos % SIZE;
                    grid[row][col] = card;
                    Card[] rowCheck = new Card[5];
                    Card[] colCheck = new Card[5];
                    for (int j = 0; j < 5; j++) {
                        if (grid[row][j] == null) {
                            rowEmptyCount++;
                        }
                        if (grid[j][col] == null) {
                            colEmptyCount++;
                        }
                        rowCheck[j] = grid[row][j];
                        colCheck[j] = grid[j][col];

                    }

                    // storing base points of row and column
                    int basePoints = 0;
                    // row base points
                    int rowPoints = system.getHandScore(rowCheck);
                    basePoints += rowPoints;
                    // checking possible points of row if only row is not full after placing card
                    rowPoints += (rowEmptyCount > 0) ? checkPoints(rowCheck, rowEmptyCount, rowPoints) : 0;
                    // col base points
                    int colPoints = system.getHandScore(colCheck);
                    basePoints += colPoints;
                    // checking possible points of column if only column is not full after placing card
                    colPoints += (colEmptyCount > 0) ? checkPoints(colCheck, colEmptyCount, colPoints) : 0;

                    // adding position into priority queue
                    pq.add(new Position(pos, basePoints, rowPoints + colPoints, rowEmptyCount + colEmptyCount));

                    // undoing grid position to null after calcualting possible scores
                    grid[row][col] = null;
                }

                // Simulation part
                long simEndTime;
                // getting count of sim plays if less than limit perform on all positions
                int simPlay = pq.size() > PRIORITY_COUNT ? PRIORITY_COUNT : pq.size();
                int totalPoints,
                 totalSims;
                Set<Integer> greedyAvailablePositions; // available postions for the simulations
                long timeRemaining = millisRemaining - (System.currentTimeMillis() - starttime); // remaining time for simulations
                long millisPerPlay = timeRemaining / (NUM_POS - numPlays - 1); // remaining time per play 
                long millisPerPosition = millisPerPlay / simPlay; // time allocated per position

                while (simPlay > 0) {
                    totalPoints = 0;
                    totalSims = 0;
                    int priorityPos = pq.poll().getPosition(); // getting higher priority position
                    greedyAvailablePositions = new HashSet<>(availablePositions);
                    greedyAvailablePositions.remove(priorityPos); // removing element from available positions
                    grid[priorityPos / SIZE][priorityPos % SIZE] = card; // placing card to grid
                    int basePoints = system.getScore(grid); // getting score of the partial filled grid
                    simEndTime = System.currentTimeMillis() + millisPerPosition; // calculating ending time 
                    while (System.currentTimeMillis() < simEndTime) {
                        totalPoints += simGreedyPlay(priorityPos, greedyAvailablePositions); // running simulations
                        totalSims++;
                    }

                    //undoing
                    grid[priorityPos / SIZE][priorityPos % SIZE] = null;

                    //averaging all simulation score
                    double averageScore = (double) totalPoints / totalSims;

                    // storing position with max score
                    if (averageScore > maxPoints) {
                        maxPoints = basePoints + averageScore;
                        bestPlays.clear();
                        bestPlays.add(priorityPos);
                    } else if (averageScore == maxPoints) {
                        bestPlays.add(priorityPos); // adding to set of best plays
                    }

                    simPlay--;
                }

                // getting best position ( breaking the tie randomly)
                rowColPosition = bestPlays.get(random.nextInt(bestPlays.size()));
                break;
        }

        // removing the position from the available
        availablePositions.remove(rowColPosition);
        numPlays++; // incrementing cards placed
        // position of the card to be returned
        int[] playPos = {rowColPosition / SIZE, rowColPosition % SIZE};
        grid[playPos[0]][playPos[1]] = card; // card placed in grid

        return playPos;
    }

    @Override
    public String getName() {
        return "MyPlayer";
    }

    /**
     * Utility function to check the possible points by giving partial rows or cols, along with emptycount and 
     * its base points
     * @param list
     * @param emptyCount
     * @param basePoints
     * @return
     */
    public int checkPoints(Card[] list, int emptyCount, int basePoints) {
        Set<Integer> ranks = new HashSet<>(); // to store unique ranks
        Set<Integer> suits = new HashSet<>(); // to store unique suits
        // storing count of each rank card list
        Map<Integer, Long> rankCount = Arrays.asList(list).stream().filter(c -> c != null).
                collect(Collectors.groupingBy(Card -> Card.getRank(), Collectors.counting())); 
        int minRank = Integer.MAX_VALUE; // used to track min of the given cards (for royal flush check)
        for (Card c : list) {
            if (c == null) {
                continue;
            }
            ranks.add(c.getRank());
            suits.add(c.getSuit());
            if (c.getRank() != 0 && c.getRank() < minRank) {
                minRank = c.getRank();
            }
        }

        int possiblePoints = 0;
        int hands = 0;

        // if there are no points
        if (basePoints == system.getHandScore(PokerHand.HIGH_CARD)) {
            possiblePoints += system.getHandScore(PokerHand.ONE_PAIR);
            hands += 1;
            boolean isThreePossible = false;
            // possible hands based on empty positions
            switch (emptyCount) {
                case 4:
                    int singleElement = ranks.iterator().next();
                    possiblePoints += system.getHandScore(PokerHand.TWO_PAIR);
                    //modification of condition
                    if (rankMap[singleElement] >= 2 || isThreeOfAKindPossible()) {
                        possiblePoints += system.getHandScore(PokerHand.THREE_OF_A_KIND);
                        isThreePossible = true;
                        hands += 1;
                    }
                    if (rankMap[singleElement] == 3) {
                        possiblePoints += system.getHandScore(PokerHand.FOUR_OF_A_KIND);
                        hands += 1;
                    }

                    if (isThreePossible) {
                        possiblePoints += system.getHandScore(PokerHand.FULL_HOUSE);
                        hands += 1;
                    }

                    break;
                case 3:
                    possiblePoints += system.getHandScore(PokerHand.TWO_PAIR);
                    hands += 1;
                    if (isThreeOfAKindPossible()) {
                        possiblePoints += system.getHandScore(PokerHand.THREE_OF_A_KIND);
                        hands += 1;

                    }
                    for (int r : ranks) {
                        if (rankMap[r] > 1) {
                            possiblePoints += system.getHandScore(PokerHand.FULL_HOUSE);
                            hands += 1;
                            break;
                        }
                    }
                    break;
                case 2:
                    int pairsPossible = 0,
                     triplets = 0;
                    for (int r : ranks) {
                        if (rankMap[r] == 1) {
                            pairsPossible++;
                        } else if (rankMap[r] == 2) {
                            triplets++;
                        }
                    }
                    if (pairsPossible == 2) {
                        possiblePoints += system.getHandScore(PokerHand.TWO_PAIR);
                        hands += 1;
                    }
                    if (triplets > 0) {
                        possiblePoints += system.getHandScore(PokerHand.THREE_OF_A_KIND);
                        hands += 1;
                    }
                    break;
                default:
                    break;
            }

         // if it already has one pair   
        } else if (basePoints == system.getHandScore(PokerHand.ONE_PAIR)) {
            switch (emptyCount) {
                case 3:
                    if (isThreeOfAKindPossible()) {
                        possiblePoints += system.getHandScore(PokerHand.FULL_HOUSE);
                        hands += 1;
                    }
                    possiblePoints += system.getHandScore(PokerHand.TWO_PAIR);
                    hands += 1;
                    if (rankMap[ranks.iterator().next()] == 2) {
                        possiblePoints += system.getHandScore(PokerHand.FOUR_OF_A_KIND);
                        hands += 1;
                    } else if (rankMap[ranks.iterator().next()] == 1 || isThreeOfAKindPossible()) {
                        possiblePoints += system.getHandScore(PokerHand.THREE_OF_A_KIND);
                        hands += 1;
                    }
                    break;
                case 2: {
                    possiblePoints += system.getHandScore(PokerHand.TWO_PAIR);
                    hands += 1;
                    int pairElement = 0, singleElement = 0;
                    for (Map.Entry<Integer, Long> entry : rankCount.entrySet()) {
                        if (entry.getValue() == 2) {
                            pairElement = entry.getKey();
                        } else {
                            singleElement = entry.getKey();
                        }
                    }
                    if (rankMap[pairElement] == 2) {
                        possiblePoints += system.getHandScore(PokerHand.FOUR_OF_A_KIND);
                        hands += 1;
                    }
                    if (rankMap[pairElement] >= 1 || rankMap[singleElement] >= 2) {
                        possiblePoints += system.getHandScore(PokerHand.THREE_OF_A_KIND);
                        possiblePoints += system.getHandScore(PokerHand.FULL_HOUSE);
                        hands += 2;
                    }
                    break;
                }
                default: {
                    int pairElement = 0;
                    for (Map.Entry<Integer, Long> entry : rankCount.entrySet()) {
                        if (entry.getValue() == 2) {
                            pairElement = entry.getKey();
                        }
                        if (rankMap[pairElement] >= 1) {
                            possiblePoints += system.getHandScore(PokerHand.THREE_OF_A_KIND);
                            hands += 1;
                        }
                        for (int r : ranks) {
                            if (r != pairElement && rankMap[r] >= 1) {
                                possiblePoints += system.getHandScore(PokerHand.TWO_PAIR);
                                hands += 1;
                                break;
                            }
                        }
                    }
                    break;
                }
            }
          // if it already has two pairs  
        } else if (basePoints == system.getHandScore(PokerHand.TWO_PAIR)) {
            for (int r : ranks) {
                if (rankMap[r] >= 1) {
                    possiblePoints += system.getHandScore(PokerHand.FULL_HOUSE);
                    hands += 1;
                }
            }

         // if list contains a three of a kind   
        } else if (basePoints == system.getHandScore(PokerHand.THREE_OF_A_KIND)) {
            int tripletElement = 0, singleElement = -1;
            for (Map.Entry<Integer, Long> entry : rankCount.entrySet()) {
                if (entry.getValue() == 3) {
                    tripletElement = entry.getKey();
                } else {
                    singleElement = entry.getKey();
                }

            }

            if (rankMap[tripletElement] == 1) {
                possiblePoints += system.getHandScore(PokerHand.FOUR_OF_A_KIND);
                hands += 1;
            }
            if ((singleElement != -1 && rankMap[singleElement] >= 1) || emptyCount == 2) {
                possiblePoints += system.getHandScore(PokerHand.FULL_HOUSE);
                hands += 1;
            }

        }

        // if there is only one type of suit in the given list
        // this shows chances for flush , straight flush and royal flush
        if (suits.size() == 1) {

            // then 1st check flush possible
            if (suitMap[suits.iterator().next()] >= emptyCount) {
                possiblePoints += system.getHandScore(PokerHand.FLUSH);
                hands += 1;
                // if flush possible then check for straight flush
                if (checkStraight(suits, true, ranks)) {
                    possiblePoints += system.getHandScore(PokerHand.STRAIGHT_FLUSH);
                    hands += 1;
                }
            }

            // then check royal flush possible
            if (minRank >= 9 && checkRoyalFlush(suits.iterator().next(), ranks)) {
                possiblePoints += system.getHandScore(PokerHand.ROYAL_FLUSH);
                hands += 1;
            }
        }

        // checking straight only
        if (checkStraight(suits, false, ranks)) {
            possiblePoints += system.getHandScore(PokerHand.STRAIGHT);
            hands += 1;
        }

        // returning average hand score or 0 if no hands
        return hands != 0 ? possiblePoints / hands : 0;
    }

    // utility function to check straights
    public boolean checkStraight(Set<Integer> suits, boolean isFlush, Set<Integer> ranks) {
        Set<Integer> temp;
        for (Set<Integer> straight : straights) {
            if (straight.containsAll(ranks)) {
                temp = new HashSet<>(straight);
                temp.removeAll(ranks);
                if (isFlush) {
                    int suit = suits.iterator().next();
                    for (Integer i : temp) {
                        if (simDeck[(suit * Card.NUM_RANKS) + i] == null) {
                            return false;
                        }
                    }
                    return true;
                } else {
                    boolean flag = true;
                    for (Integer i : temp) {
                        if (rankMap[i] == 0) {
                            flag = false;
                        }
                    }
                    if (flag == true) {
                        return true;
                    }
                }

            }

        }
        return false;
    }

    // utility function to check royal flush
    public boolean checkRoyalFlush(int suit, Set<Integer> ranks) {
        if (!ranks.contains(0) && simDeck[(suit * Card.NUM_RANKS) + 0] == null) {
            return false;
        }
        for (int j = 9; j < 13; j++) {
            if (!ranks.contains(j) && simDeck[(suit * Card.NUM_RANKS) + j] == null) {
                return false;
            }
        }

        return true;

    }

    public boolean isThreeOfAKindPossible() {
        return IntStream.of(rankMap).anyMatch(x -> x >= 3);
    }

    //simulation part
    public int simGreedyPlay(int position, Set<Integer> availablePositions) {
        int remainingPlays = availablePositions.size(), col = 0, row = 0;
        List<Integer> bestPlays = new ArrayList<>();
        int[] undoTrack = new int[remainingPlays]; // storing positions to perform undoing after simulations
        int maxScore = Integer.MIN_VALUE;
        List<Card> deck = Arrays.asList(simDeck).stream().filter(c -> c != null).collect(Collectors.toList());
        int depth = remainingPlays > DEPTH ? DEPTH : remainingPlays; // setting depth if remaining plays are greater than limit
        for (int i = 0; i < depth; i++) {
            int randomIndex = random.nextInt(deck.size());
            Card card = deck.get(randomIndex);
            bestPlays.clear();
            maxScore = Integer.MIN_VALUE;
            for (int pos : availablePositions) {
                row = pos / SIZE;
                col = pos % SIZE;
                grid[row][col] = card;
                int score = system.getScore(grid);
                if (score > maxScore) {
                    maxScore = score;
                    bestPlays.clear();
                    bestPlays.add(pos);
                } else if (score == maxScore) {
                    bestPlays.add(pos);
                }

                grid[row][col] = null;
            }

            deck.remove(randomIndex);
            int checkr = random.nextInt(bestPlays.size());
            int selectedPos = bestPlays.get(checkr);
            undoTrack[i] = selectedPos;
            availablePositions.remove(selectedPos);
            grid[selectedPos / SIZE][selectedPos % SIZE] = card;

        }

        int finalScore = system.getScore(grid); // getting final score of grid

        //performing undoing
        for (int i = 0; i < depth; i++) {
            grid[undoTrack[i] / SIZE][undoTrack[i] % SIZE] = null;
        }

        return finalScore;

    }

    public static void main(String[] args) {
        PokerSquaresPointSystem system = PokerSquaresPointSystem.getBritishPointSystem();
        System.out.println(system);
        new PokerSquares(new MyPlayer(), system).play();
    }

}

/**
 * To store position details 
 */
class Position {

    private int position;
    private int basePoints;
    private int totalPoints;
    private int emptyCount;

    public Position(int position, int basePoints, int totalPoints, int emptyCount) {
        this.position = position;
        this.basePoints = basePoints;
        this.totalPoints = totalPoints;
        this.emptyCount = emptyCount;

    }

    public int getEmptyCount() {
        return emptyCount;
    }

    public void setEmptyCount(int emptyCount) {
        this.emptyCount = emptyCount;
    }

    public int getPosition() {
        return position;
    }

    public void setPosition(int position) {
        this.position = position;
    }

    public int getBasePoints() {
        return basePoints;
    }

    public void setBasePoints(int basePoints) {
        this.basePoints = basePoints;
    }

    public int getTotalPoints() {
        return totalPoints;
    }

    public void setTotalPoints(int totalPoints) {
        this.totalPoints = totalPoints;
    }
}

// comparator used to sort the positions based on the totalpoints, basepoints and emptycounts
// ties are solved randomly
class PositionComparator implements Comparator<Position> {

    @Override
    public int compare(Position p1, Position p2) {
        if (p2.getTotalPoints() - p1.getTotalPoints() == 0) {
            if (p1.getBasePoints() - p2.getBasePoints() == 0) {
                if (p2.getEmptyCount() - p1.getEmptyCount() == 0) {
                    return new Random().nextBoolean() == true ? 1 : -1;
                }
                return p1.getEmptyCount() - p2.getEmptyCount();
            }
            return p2.getBasePoints() - p1.getBasePoints();
        }
        return p2.getTotalPoints() - p1.getTotalPoints();
    }
}
