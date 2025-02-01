import { Table } from "poker-ts";
import { BroadcastPayload, BroadcastType, FxnClient } from "./fxnClient.ts";
import Poker, { Action, Card } from "poker-ts/dist/facade/poker";
import assert from "assert";
import { randomInt } from "crypto";

declare type SeatIndex = number;
declare type PublicKey = string;
declare type BetSize = number;
declare type RoundOfBetting = 'preflop' | 'flop' | 'turn' | 'river';
export declare type GameStateString = "prehand" | RoundOfBetting | "showdown" | "posthand";
export declare type ActionHistory = Array<ActionHistoryEntry>;

enum HandRanking {
    HIGH_CARD = 0,
    PAIR = 1,
    TWO_PAIR = 2,
    THREE_OF_A_KIND = 3,
    STRAIGHT = 4,
    FLUSH = 5,
    FULL_HOUSE = 6,
    FOUR_OF_A_KIND = 7,
    STRAIGHT_FLUSH = 8,
    ROYAL_FLUSH = 9
}

const HandRankingStr = [
    "High Card",
    "Pair",
    "Two Pair",
    "Three of a Kind",
    "Straight",
    "Flush",
    "Full House",
    "Four of a Kind",
    "Straight Flush",
    "Royal Flush"
];

export interface ActionHistoryEntry {
    roundOfBetting: RoundOfBetting,
    name: string,
    action: Action,
    betSize: BetSize
};

export interface LegalActions {
    actions: Action[],
    chipRange?: {
        min: BetSize,
        max: BetSize
    }
}

interface Winner {
    seatIndex: SeatIndex,
    ranking: HandRanking,
    winnings: number
}

interface ForcedBets {
    ante: BetSize,
    bigBlind: BetSize,
    smallBlind: BetSize
}

// Stuff that everyone at the table can know
export interface TableState {
    // Static
    forcedBets: ForcedBets, // Blinds and ante
    numSeats: number, // Total number of seats

    // Changes per-hand
    emptySeats: Array<SeatIndex>, // Index of each empty seat
    button: SeatIndex, // Who is the dealer
    bigBlindSeat: SeatIndex,
    smallBlindSeat: SeatIndex,

    // Changes per-action
    playerToActName: string, // The name of the player to act
    playerToActSeat: number,
    pots: Array<number>, // The size of each pot
    communityCards: Array<Card>,
    gameStateString: GameStateString,

    // Changes per-showdown
    winners: Array<Winner>
}

// Stuff that should be kept secret from other players
export interface PlayerState {
    // Static
    publicKey: PublicKey,
    seat: SeatIndex
    name: string,

    // Changes per-hand
    holeCards: Card[],
    isDealer: boolean,
    isSmallBlind: boolean,
    isBigBlind: boolean,

    // Changes per-action
    toAction: boolean // is it their turn
    legalActions: LegalActions
    stack: number,
    currentBet: number,
    isFolded: boolean,

    // Changes per-showdown
    isWinner: boolean
}

const ANTE: BetSize = 0;
const BIG_BLIND: BetSize = 10;
const SMALL_BLIND: BetSize = 5;
const MAX_PLAYERS: number = 9; // Max of 23 set by poker-ts

export class PokerManager {
    private DEBUG: boolean;
    private DEBUG_seatedPlayers: boolean;
    private table: Poker;
    private tableState: TableState;
    private playerStates: PlayerState[];
    private actionHistory: ActionHistory;
    private playerKeys: Map<SeatIndex, PublicKey>;
    private playerSeats: Map<PublicKey, SeatIndex>;
    public readonly TABLE_EMPTY_DELAY: number = 30 * 1000; // 30s delay
    private tableEmptyTimer: NodeJS.Timeout | null = null;
    public readonly NEW_HAND_DELAY: number = 10 * 1000; // 5s delay
    private newHandTimer: NodeJS.Timeout | null = null;
    public readonly HAND_LOOP_DELAY: number = 5 * 1000; // 5s delay
    private handLoopTimer: NodeJS.Timeout | null = null;

    constructor(private fxnClient: FxnClient) {
        this.DEBUG = false; // DEBUG MODE

        this.table = new Table({ante: ANTE, bigBlind: BIG_BLIND, smallBlind: SMALL_BLIND}, MAX_PLAYERS);
        this.tableState = this.initializeTableState();
        this.playerStates = new Array<PlayerState>(MAX_PLAYERS);
        this.actionHistory = new Array<ActionHistoryEntry>();
        this.playerKeys = new Map<SeatIndex, PublicKey>();
        this.playerSeats = new Map<PublicKey, SeatIndex>();
        this.startNewHand();
    }

    private initializeTableState(): TableState {
        return {
            emptySeats: new Array<SeatIndex>(),
            forcedBets: {ante: -1, bigBlind: -1, smallBlind: -1},
            numSeats: -1,
            button: -1,
            playerToActName: "",
            playerToActSeat: -1,
            bigBlindSeat: -1,
            smallBlindSeat: -1,
            pots: new Array<number>(),
            communityCards: new Array<Card>(),
            gameStateString: "prehand",
            winners: new Array<Winner>()
        }
    }

    private async startNewHand() {
        if (this.newHandTimer) {
            clearTimeout(this.newHandTimer);
        }

        console.log("Starting a new hand.");

        if (this.DEBUG) {
            if (!this.DEBUG_seatedPlayers) {
                // Fill a few seats for testing
                this.addPlayer("Key1", 1, 300, "Brett");
                this.addPlayer("Key2", 3, 300, "Kara");
                this.addPlayer("Key3", 5, 300, "Claire");
                this.addPlayer("Key4", 7, 300, "Liam");

                this.DEBUG_seatedPlayers = true;

                this.tableState.emptySeats = this.getEmptySeats();
            }
        } else {
            await this.standUpUnresponsivePlayers();
            await this.trySeatingPlayers();
        }

        if (this.getFilledSeats().length < 2) {
            // There are less than 2 players at the table, check again in X seconds
            if (this.tableEmptyTimer) {
                clearTimeout(this.tableEmptyTimer);
            }

            console.log(`Not enough players, trying again in ${this.TABLE_EMPTY_DELAY / 1000} seconds.`);
            this.tableEmptyTimer = setTimeout(() => this.startNewHand(), this.TABLE_EMPTY_DELAY);
        }
        else
        {
            // We have at least 2 players and can start the hand
            this.updateStateForNewHand();

            // Start first hand
            this.startHand();
        }
    }

    // Stands up any players who don't respond to an isAlive ping
    private async standUpUnresponsivePlayers() {
        const seatedPlayers = this.getSeatedPlayerStates();
        if (seatedPlayers.length == 0)
            return;

        const aliveSubscribers = await this.fxnClient.getAliveSubscribers();
        if (aliveSubscribers.length == 0)
            return;

        const aliveKeys = aliveSubscribers.map((s) => {return s.subscriber.toString()});
        seatedPlayers.forEach((playerState) => {
            if (!aliveKeys.includes(playerState.publicKey)) {
                this.removePlayer(playerState.publicKey);
            }
        });

        // Update table state after kicking players
        this.tableState.emptySeats = this.getEmptySeats();
    }

    private async trySeatingPlayers() {
        if (this.getEmptySeats().length > 0) {
            // We have empty seats, seat any alive subscribers
            const aliveSubscribers = await this.fxnClient.getAliveSubscribers();
            if (aliveSubscribers.length == 0) {
                console.log("No live subscribers.");
            } else {
                aliveSubscribers.forEach((subscriberDetails) => {
                    const publicKey = subscriberDetails.subscriber.toString();
                    if (!this.isSeated(publicKey)) {
                        const seatIndex = this.getEmptySeats().pop();
                        const buyIn = 300;
                        this.addPlayer(publicKey, seatIndex, buyIn, publicKey);
                    }
                });
            }
        }

        // Update table state after seating subscribers
        this.tableState.emptySeats = this.getEmptySeats();
    }

    private async startHand() {
        // Start the hand internally
        this.table.startHand();
        assert(this.table.isHandInProgress());
        assert(this.table.isBettingRoundInProgress());

        console.log("Hand started.");

        this.updateStateAfterInitialDeal();

        // At this point we are pre-flop, waiting for the player after the big blind to act
        this.newHandLoop();
    }

    private updateStateForNewHand(log: boolean = false) {
        // Reset table state for new hand
        this.tableState.numSeats = this.table.numSeats();
        this.tableState.forcedBets = this.table.forcedBets();
        this.tableState.pots = [0];
        this.tableState.communityCards = [];
        this.tableState.winners = [];

        if (log) {
            console.log("Table state for new hand:");
            console.log(this.tableState);
        }

        // Reset player states for new game
        if (log) {
            console.log("Player states for new hand:");
        }
        this.getFilledSeats().forEach((seatIndex) => {
            this.playerStates[seatIndex].toAction = false;
            this.playerStates[seatIndex].isFolded = false;
            this.playerStates[seatIndex].isDealer = false;
            this.playerStates[seatIndex].isSmallBlind = false;
            this.playerStates[seatIndex].isBigBlind = false;
            this.playerStates[seatIndex].currentBet = -1;
            this.playerStates[seatIndex].isWinner = false;
            this.playerStates[seatIndex].holeCards = [];
            this.playerStates[seatIndex].legalActions = null;

            if (log) {
                console.log(this.playerStates[seatIndex]);
            }
        });

        // Reset action history after new game
        this.actionHistory = new Array<ActionHistoryEntry>();
        if (log) {
            console.log("Action history for new hand:");
            console.log(this.actionHistory);
        }
    }

    private updateStateAfterInitialDeal(log: boolean = false) {
        // Update table state string
        this.tableState.gameStateString = "preflop";

        // Update dealer and blind seats
        const dealerSeat = this.table.button();
        const smallBlindSeat = this.getNextFilledSeat(dealerSeat);
        const bigBlindSeat = this.getNextFilledSeat(smallBlindSeat);
        this.tableState.button = dealerSeat;
        this.tableState.smallBlindSeat = smallBlindSeat;
        this.tableState.bigBlindSeat = bigBlindSeat;

        // Update the player to act
        const playerToActSeat = this.table.playerToAct();
        this.tableState.playerToActName = this.getPlayerName(playerToActSeat);
        this.tableState.playerToActSeat = playerToActSeat;

        // Update pots
        this.updatePots();

        if (log) {
            console.log("Table state after initial deal:");
            console.log(this.tableState);
        }

        // Update player states
        if (log) {
            console.log("Player states after initial deal:");
        }
        this.getFilledSeats().forEach((seatIndex) => {
            let playerState = this.playerStates[seatIndex];

            // Update bools
            playerState.isDealer = seatIndex == this.tableState.button;
            playerState.isBigBlind = seatIndex == this.tableState.bigBlindSeat;
            playerState.isSmallBlind = seatIndex == this.tableState.smallBlindSeat;

            // Update hole cards
            playerState.holeCards = this.table.holeCards()[seatIndex];;

            // Update stacks and bets
            playerState.stack = this.table.seats()[seatIndex].stack;
            playerState.currentBet = this.table.seats()[seatIndex].betSize;

            // Update legal actions
            const toAct = playerToActSeat == seatIndex;
            playerState.toAction = toAct;
            playerState.legalActions = toAct ? this.table.legalActions() : null;

            if (log) {
                console.log(this.playerStates[seatIndex]);
            }
        });
    }

    private updatePots(log: boolean = false) {
        const roundOfBetting = this.table.roundOfBetting()
        if (roundOfBetting == "preflop") {
            let potSize = 0;
            this.getFilledSeats().forEach((seatIndex) => {
                potSize += this.table.seats()[seatIndex].betSize;
            });
            this.tableState.pots[0] = potSize;
        } else {
            this.tableState.pots = this.table.pots().map(pot => pot.size);
        }

        if (log) {
            console.log(`Pots updated during ${roundOfBetting}`);
            console.log(this.table.pots());
            console.log(this.tableState.pots);
        }
    }

    private async newHandLoop(): Promise<void> {
        if (this.handLoopTimer) {
            clearTimeout(this.handLoopTimer);
        }

        if (this.table.isHandInProgress()) {
            if (this.table.isBettingRoundInProgress()) {

                if (this.DEBUG) { // Hard coded actions
                    const legalActions = this.table.legalActions();
                    console.log("Randomly selecting an action and bet from the following:");
                    console.log(legalActions);

                    const actions = legalActions.actions;
                    const chipRange = legalActions.chipRange;

                    let action, betSize;
                    if (actions.length > 0) {
                        const actionIdx = randomInt(legalActions.actions.length)
                        action = actions[actionIdx];
                        if (chipRange && (action == "raise" || action == "bet")) {
                            if (chipRange.min == chipRange.max) {
                                betSize = chipRange.min;
                            } else {
                                betSize = randomInt(chipRange.min, chipRange.max);
                            }
                        }
                    }
                    this.takeAction([action, betSize]);
                } else {
                    // Get action from subscriber
                    const playerAction = await this.getActionFromSubscriber();
                    this.takeAction(playerAction);
                }

                this.updateStateAfterPlayerAction();
            } else {
                console.log("Betting round over.");
                this.table.endBettingRound();

                this.updateStateAfterBettingRound();

                if (this.table.areBettingRoundsCompleted()) {
                    this.updateStateBeforeShowdown();

                    this.table.showdown();
                    this.updateStateAfterShowdown();
                }
            }
        } else {
            // Hand is over

            // Update state
            this.tableState.gameStateString = "posthand";

            this.tableState.winners.forEach((winner) => {
                console.log(`${this.playerStates[winner.seatIndex].name} wins ${winner.winnings} with a ${HandRankingStr[winner.ranking]}!`);
            })

            if (!this.DEBUG) {
                // Stand up dead subscribers between hands
                await this.standUpUnresponsivePlayers();
            }
    
            console.log(`Hand over! Starting new hand in ${this.NEW_HAND_DELAY / 1000}s.`);
            this.newHandTimer = setTimeout(() => {this.startNewHand()}, this.NEW_HAND_DELAY);

            if (!this.DEBUG) {
                // Try seating new connections before the next hand
                this.trySeatingPlayers();
            }

            // don't start the hand loop again
            return;
        }

        console.log(`Broadcasting again in ${this.HAND_LOOP_DELAY / 1000} seconds.`);
        this.handLoopTimer = setTimeout(() => {this.newHandLoop()}, this.HAND_LOOP_DELAY);
    }

    private takeAction(playerAction: [Action, BetSize]) {
        const action = playerAction[0];
        const betSize = playerAction[1];

        // Get the state of the table before taking the action
        const roundOfBetting = this.table.roundOfBetting();

        // Get the player's seat
        const seatIndex = this.table.playerToAct();

        // Add their action to the actionHistory
        const name = this.playerStates[seatIndex].name;
        this.actionHistory.push({roundOfBetting, name, action, betSize});
        
        // Update the player's isFolded
        this.playerStates[seatIndex].isFolded = action == "fold";

        // Reset their legal actions
        this.playerStates[seatIndex].legalActions = null;

        // Log the action to the console
        console.log("Player: " + name + " Action: " + action + " Bet: " + betSize);

        // process the action in the internal table
        this.table.actionTaken(action, betSize);
    }

    private async getActionFromSubscriber(): Promise<[Action, BetSize]> {
        // Get player to act info
        const seatIndex = this.table.playerToAct();
        const publicKey = this.playerKeys.get(seatIndex);

        // Get subscription
        const aliveSubscribers = await this.fxnClient.getAliveSubscribers();
        const subscriberDetails = aliveSubscribers.find(s => s.subscriber.toString() == publicKey);
        if (!subscriberDetails) {
            // Subscriber is not alive
            console.log(`Subscriber not alive to take their turn, auto-folding. ${publicKey}.`);
            return ["fold", 0];
        }

        const recipient = subscriberDetails.subscription.recipient;
        console.log(`Prompting ${recipient} for action`);

        // Construct the payload
        const payload: BroadcastPayload = {
            type: BroadcastType.Query,
            content: {
                tableState: this.tableState,
                playerState: this.playerStates[seatIndex],
                actionHistory: this.actionHistory
            }
        }

        let action: Action = "fold";
        let betSize = 0;
                
        // Await their response
        await this.fxnClient.broadcastToSubscriber(payload, subscriberDetails)
        .then(async (response) => {
            if (response.ok) {
                // Parse their chosen action
                const responseData = await response.json();

                if (this.validateResponseData(responseData)) {
                    action = responseData.action;
                    betSize = responseData.betSize;
                } else {
                    console.log(`Invalid response data from ${recipient}. Auto-folding.`);
                    console.log(responseData);
                }
            }
        }).catch((error) => {
            console.log(`Error fetching action from ${recipient}. Auto-folding.`, error);
        });

        return [action, betSize];
    }

    private updateStateAfterPlayerAction(log: boolean = false) {
        if (this.table.isBettingRoundInProgress()) {
            // We are still in the betting round

            // Update player to act
            const playerToActSeat = this.table.playerToAct();
            this.tableState.playerToActSeat = playerToActSeat;
            this.tableState.playerToActName = this.getPlayerName(playerToActSeat);

            // Update pots
            this.updatePots();

            if (log) {
                console.log(`Table state after player action:`);
                console.log(this.tableState);
            }

            // Update player states
            if (log) {
                console.log("Player states after player action:");
            }
            this.getFilledSeats().forEach((seatIndex) => {
                let playerState = this.playerStates[seatIndex];

                // Update stacks and bets
                playerState.currentBet = this.table.seats()[seatIndex].betSize;
                playerState.stack = this.table.seats()[seatIndex].stack;

                // Update legal actions
                const toAct = playerToActSeat == seatIndex;
                playerState.toAction = toAct;
                playerState.legalActions = toAct ? this.table.legalActions() : null;

                if (log) {
                    console.log(this.playerStates[seatIndex]);
                }
            });
        } else {
            // The betting round is over, we'll update in updateStateAfterBettingRound
            return;
        }
    }

    private updateStateAfterBettingRound(log: boolean = false) {
        if (!this.table.areBettingRoundsCompleted()) {
            // We have started a new betting round

            // Update state
            this.tableState.gameStateString = this.table.roundOfBetting();

            // Update community cards
            this.tableState.communityCards = this.table.communityCards();

            // Update player to act
            const playerToActSeat = this.table.playerToAct();
            this.tableState.playerToActSeat = playerToActSeat;
            this.tableState.playerToActName = this.getPlayerName(playerToActSeat);

            // Update pots
            this.updatePots();

            if (log) {
                console.log(`Table state after betting round:`);
                console.log(this.tableState);
            }

            // Update player states
            if (log) {
                console.log("Player states after betting round:");
            }
            this.getFilledSeats().forEach((seatIndex) => {
                let playerState = this.playerStates[seatIndex];

                // Update stacks and bets
                playerState.currentBet = this.table.seats()[seatIndex].betSize;
                playerState.stack = this.table.seats()[seatIndex].stack;

                // Update legal actions
                const toAct = playerToActSeat == seatIndex;
                playerState.toAction = toAct;
                playerState.legalActions = toAct ? this.table.legalActions() : null;

                if (log) {
                    console.log(this.playerStates[seatIndex]);
                }
            });
        } else {
            // We have finished the betting rounds and are about to showdown
        }
    }
    private updateStateBeforeShowdown(log: boolean = false) {
        console.log("Starting showdown.");

        this.tableState.gameStateString = "showdown";
        this.updatePots();

        // If there is only one pot with one eligible player, they won't show up in winners() so add them here
        const pots = this.table.pots();
        if (pots.length == 1 && pots[0].eligiblePlayers.length == 1) {
            const seatIndex = pots[0].eligiblePlayers[0];
            const winnings = pots[0].size;
            const winnerHand = this.playerStates[seatIndex].holeCards.concat(this.table.communityCards());
            this.tableState.winners.push({
                seatIndex: seatIndex,
                ranking: this.getHandRanking(winnerHand),
                winnings: winnings
            });

            this.playerStates[seatIndex].isWinner = true;
        }

        if (log) {
            console.log("Table state before showdown:");
            console.log(this.tableState);

            console.log("Player states before showdown:");
            this.getFilledSeats().forEach((seatIndex) => {
                console.log(this.playerStates[seatIndex]);
            });
        }
    }

    private updateStateAfterShowdown(log: boolean = false) {
        if (this.table.winners().length != 0) {
            this.table.winners().forEach((pot, potIndex) => {
                pot.forEach((winner) => {
                    const seatIndex = winner[0];
                    const winnings = this.tableState.pots[potIndex];
                    const winnerHandRanking = winner[1].ranking;
                    this.tableState.winners.push({
                        seatIndex: seatIndex,
                        ranking: winnerHandRanking,
                        winnings: winnings
                    });

                    this.playerStates[seatIndex].isWinner = true;
                })
            })
        }

        if(log) {
            console.log("Table state after showdown:");
            console.log(this.tableState);

            console.log("Player states after showdown:");
            this.getFilledSeats().forEach((seatIndex) => {
                console.log(this.playerStates[seatIndex]);
            });
        }
    }

    public getTableState(): TableState {
        return this.tableState;
    }

    private addPlayer(publicKey: PublicKey, seatIndex: SeatIndex, buyIn: number, name: string)
    {
        this.table.sitDown(seatIndex, buyIn);
        this.playerKeys.set(seatIndex, publicKey);
        this.playerSeats.set(publicKey, seatIndex);
        this.playerStates[seatIndex] = {
            publicKey: publicKey,
            seat: seatIndex,
            name: name,

            holeCards: new Array<Card>(),
            isDealer: false,
            isSmallBlind: false,
            isBigBlind: false,

            toAction: false,
            legalActions: null,
            stack: -1,
            currentBet: -1,
            isFolded: false,

            isWinner: false
        }

        console.log(`Seated ${publicKey} at chair ${seatIndex} with ${buyIn} chips.`);
    }

    private removePlayer(publicKey: PublicKey) {
        const seatIndex = this.getSeatIndex(publicKey);
        this.playerKeys.delete(seatIndex);
        this.playerSeats.delete(publicKey);
        this.playerStates[seatIndex] = null;

        this.table.standUp(seatIndex);
    }

    private getSeatIndex(publicKey: PublicKey): SeatIndex {
        const seatIndex = this.playerSeats.get(publicKey);
        assert(seatIndex, `Error: public key ${publicKey} is not seated.`);

        return seatIndex;
    }

    private getPlayerName(seatIndex: SeatIndex): string {
        return this.playerStates[seatIndex].name;
    }

    private isSeated(publicKey: PublicKey): boolean {
        return this.playerSeats.get(publicKey) ? true : false;
    }

    public getSeatedPlayerStates(): Array<PlayerState> {
        return this.getFilledSeats().map((seatIndex) => {
            return this.playerStates[seatIndex];
        });
    }

    private getEmptySeats(): number[] {
        let emptySeats = new Array<number>();
        this.table.seats().forEach((seat, index) => {
            if (seat == null)
                emptySeats.push(index);
        });
        return emptySeats;
    }

    private getFilledSeats(): number[] {
        let filledSeats = new Array<number>();
        this.table.seats().forEach((seat, index) => {
            if (seat != null)
                filledSeats.push(index);
        });
        return filledSeats;
    }

    // Return the player who's turn is after this seat
    private getNextFilledSeat(seatIndex: SeatIndex): SeatIndex {
        assert(this.table.seats()[seatIndex] != null);

        const seats = this.table.seats();
        do {
            seatIndex++
            if (seatIndex === seats.length)
                seatIndex = 0
        } while(seats[seatIndex] === null)
        
        return seatIndex;
    }

    private getHandRanking(cards: Card[]): HandRanking {
        // TODO: calculate the hand ranking based on hole + community
        return HandRanking.HIGH_CARD;
    }

    private validateResponseData(responseData: any): boolean {
        let validAction = false;
        let validBetSize = false;
        if (responseData) {
            const legalActions = this.table.legalActions();
            if (responseData.action && legalActions.actions.includes(responseData.action)) {
                validAction = true;
                if (legalActions.chipRange) {
                    const min = legalActions.chipRange.min;
                    const max = legalActions.chipRange.max;
                    if (responseData.betSize && responseData.betSize >= min && responseData.betSize <= max) {
                        validBetSize = true;
                    }
                } else {
                    validBetSize = true;
                }
            }
        }
        
        return validAction && validBetSize;
    }
}