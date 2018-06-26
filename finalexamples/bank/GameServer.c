#include "stdlib.h"
#include "sockets.h"
#include "threading.h"
//#include "bool.h"
#include "stringBuffers.h"
#include "limits.h"

struct game {
  struct string_buffer* name;
  struct socket* socket;
  struct game* next;
};

struct game_list {
  struct game* head;
  int count;
};

struct session {
  struct socket* socket;
  struct game_list* games;
  struct mutex* mutex;
};

void start_session(struct session* session);

bool create_game(struct socket* socket, struct mutex* mutex, struct game_list* games)
//@requires true;
//@ensures true;
{
  mutex_acquire(mutex);
  if(games->count == INT_MAX) {
    mutex_release(mutex);
    return false;
  } else {
    struct string_buffer* name = create_string_buffer();
    struct game* new_game = malloc(sizeof(struct game));
    if(new_game == 0) abort();
    socket_write_string(socket, "Enter the name of your game.\r\n");
    socket_read_line(socket, name);
    new_game->name = name;
    new_game->socket = socket;
    socket_write_string(socket, "Game created, waiting for other player...\r\n");
    new_game->next = games->head;
    games->head = new_game;
    games->count = games->count + 1;
    mutex_release(mutex);
    return true;
  }
}

void show_games_helper(struct socket* socket, struct game* game, int count) 
//@requires true;
//@ensures true;
{
  if(count == 0) {
  } else {
    socket_write_string_buffer(socket, game->name);
    socket_write_string(socket, "\r\n");
    show_games_helper(socket, game->next, count - 1);
  }
}

void show_games(struct socket* socket, struct mutex* mutex, struct game_list* games)
//@requires true;
//@ensures true;
{
  mutex_acquire(mutex);
  socket_write_string(socket, "There are ");
  socket_write_integer_as_decimal(socket, games->count);
  socket_write_string(socket, " available games:\r\n");
  show_games_helper(socket, games->head, games->count);
  mutex_release(mutex);
}

enum rps { rock, paper, scissors };

int get_rock_paper_or_scissors(struct socket* socket)
//@requires true;
//@ensures true;
{
  int choice = -1;
  socket_write_string(socket, "Enter a rock (0), paper (1) or scissors (2).\r\n");
  choice = socket_read_nonnegative_integer(socket);
  while(choice != rock && choice != paper && choice != scissors) 
  {
    socket_write_string(socket, "Try again.\r\n");
    choice = socket_read_nonnegative_integer(socket);
  }
  socket_write_string(socket, "Waiting for other player ...\r\n");
  return choice;
}

struct rps_session {
  struct socket* socket;
  int result;
};

void get_rock_paper_or_scissors_async(struct rps_session* rps_session)
//@requires true;
//@ensures true;
{
  int tmp = get_rock_paper_or_scissors(rps_session->socket);
  rps_session->result = tmp;
}

void play_game(struct socket* socket1, struct socket* socket2)
//@requires true;
//@ensures true;
{
  bool finished = false;
  while(! finished)
  {
    int choice1; int choice2; struct thread* thread;
    struct rps_session* rps_session = malloc(sizeof(struct rps_session));
    if(rps_session == 0) abort();
    rps_session->socket = socket1;
    thread = thread_start_joinable(get_rock_paper_or_scissors_async, rps_session);
    choice2 = get_rock_paper_or_scissors(socket2);
    thread_join(thread);
    choice1 = rps_session->result;
    free(rps_session); 
    if(choice1 == choice2) {
      socket_write_string(socket1, "A draw! Try again.\r\n");
      socket_write_string(socket2, "A draw! Try again.\r\n");
    } else {
      finished = true;
      if(choice1 == rock && choice2 == scissors || 
         choice1 == paper && choice2 == rock || 
         choice1 == scissors && choice2 == paper) 
      {
        socket_write_string(socket1, "You win.\r\n");
        socket_write_string(socket2, "You lose.\r\n");
      } else {
        socket_write_string(socket2, "You win.\r\n");
        socket_write_string(socket1, "You lose.\r\n");
      }
    }
  }
}

void join_game_core(struct socket* socket, struct mutex* mutex, struct game_list* games, struct game* joined_game)
//@requires true;
//@ensures true;
{
  struct session* session; struct thread* thread;
  socket_write_string(socket, "You have joined ");
  socket_write_string_buffer(socket, joined_game->name);
  socket_write_string(socket, ".\r\n");
  socket_write_string(joined_game->socket, "Another player joined your game.\r\n");
  string_buffer_dispose(joined_game->name);
  play_game(joined_game->socket, socket);
  session = malloc(sizeof(struct session));
  if(session == 0) abort();
  session->socket = joined_game->socket;
  session->mutex = mutex;
  session->games = games;
  thread_start(start_session, session);
  free(joined_game);
}

void join_game(struct socket* socket, struct mutex* mutex, struct game_list* games)
//@requires true;
//@ensures true;
{
  struct game* joined_game = 0;
  mutex_acquire(mutex);
  if(games->head == 0) {
    socket_write_string(socket, "No game is available.\r\n");
    mutex_release(mutex);
  } else {
    joined_game = games->head;
    games->head = joined_game->next;
    games->count = games->count - 1;
    mutex_release(mutex);
    join_game_core(socket, mutex, games, joined_game);
  }
}

struct game* select_game_helper(struct game* game, int choice) 
//@requires true;
//@ensures true;
{
  struct game* joined_game;
  if(choice == 1) {
    joined_game = game->next;
    game->next = joined_game->next;
  } else {
    joined_game = select_game_helper(game->next, choice - 1);
  }
  return joined_game;
}

void join_selected_game(struct socket* socket, struct mutex* mutex, struct game_list* games)
//@requires true;
//@ensures true;
{
  struct game* joined_game = 0;
  mutex_acquire(mutex);
  if(games->count == 0) {
    socket_write_string(socket, "No game is available.\r\n");
    mutex_release(mutex);
  } else {
    int choice;
    socket_write_string(socket, "The following games are available.\r\n");
    show_games_helper(socket, games->head, games->count);
    socket_write_string(socket, "Enter the number of the game you want to join (between 1 and ");
    socket_write_integer_as_decimal(socket, games->count);
    socket_write_string(socket, ").\r\n");
    choice = socket_read_nonnegative_integer(socket);
    while(choice < 1 || choice > games->count)
    {
      socket_write_string(socket, "Invalid choice. Try again.\r\n");
      choice = socket_read_nonnegative_integer(socket);
    }
    if(choice == 1) {
      joined_game = games->head;
      games->head = joined_game->next;
    } else {
      joined_game = select_game_helper(games->head, choice-1);
    }
    games->count = games->count - 1;
    mutex_release(mutex);
    join_game_core(socket, mutex, games, joined_game);
  }
}

// Verification of the function create_game_last is optional.
bool create_game_last(struct socket* socket, struct mutex* mutex, struct game_list* games) 
//@requires true;
//@ensures true;
{
  struct string_buffer* name = create_string_buffer();
  struct game* new_game = malloc(sizeof(struct game));
  if(new_game == 0) abort();
  socket_write_string(socket, "Enter the name of your game.\r\n");
  socket_read_line(socket, name);
  new_game->name = name;
  new_game->socket = socket;
  new_game->next = 0;
  socket_write_string(socket, "Game created, waiting for other player...\r\n");
  mutex_acquire(mutex);
  if(games->count == INT_MAX) {
    mutex_release(mutex);
    free(new_game);
    string_buffer_dispose(name);
    return false;
  } else {
    if(games->head == 0) {
      games->head = new_game;
      games->count = games->count + 1;
      mutex_release(mutex);
    } else {
      struct game* current = games->head;
      while(current->next != 0) 
      {
        current = current->next;
      }
      current->next = new_game;
      games->count = games->count + 1;
      mutex_release(mutex);
    }
    return true;
  }
}

void main_menu(struct socket* socket, struct mutex* mutex, struct game_list* games) 
//@requires true;
//@ensures true;
{
  bool quit = false;
  while(! quit) 
  {
    int choice = 0;
    socket_write_string(socket, "What would you like to do?\r\n");
    socket_write_string(socket, "1. Create a new game.\r\n");
    socket_write_string(socket, "2. Show all available games.\r\n");
    socket_write_string(socket, "3. Join an existing game.\r\n");
    socket_write_string(socket, "4. Select and join an existing game.\r\n");
    socket_write_string(socket, "5. Quit.\r\n");
    socket_write_string(socket, "6. Create a new game (optional).\r\n");
    choice = socket_read_nonnegative_integer(socket);
    if(choice == 1) {
      bool success = create_game(socket, mutex, games);
      if(success) {
        quit = true;
      } else {
        socket_write_string(socket, "Insufficient space. Try again later.");
      }
    } else if (choice == 2) {
      show_games(socket, mutex, games);
    } else if (choice == 3) {
      join_game(socket, mutex, games);
    } else if (choice == 4) {
      join_selected_game(socket, mutex, games);
    } else if (choice == 5) {
      socket_write_string(socket, "Bye!\r\n");
      socket_close(socket);
      quit = true;
    } else if (choice == 6) {
      // place the code between begin and end in comments if you do not verify the optional function create_game_last
      // <begin>
      bool success = create_game_last(socket, mutex, games); 
      if(success) {
        quit = true;
      } else {
        socket_write_string(socket, "Insufficient space. Try again later.");
      }
      // <end>
    } else {
      socket_write_string(socket, "Invalid choice. Try again.\r\n");
    }
  }
}

void start_session(struct session* session)
//@requires true;
//@ensures true;
{
  main_menu(session->socket, session->mutex, session->games);
  free(session);
}

int main()
//@requires true;
//@ensures true;
{
  struct mutex* mutex; struct server_socket* ss;
  struct game_list* games = malloc(sizeof(struct game_list));
  if(games == 0) abort();
  games->head = 0;
  games->count = 0;
  mutex = create_mutex();
  ss = create_server_socket(1234);
  while(true)
  {
    struct thread* thread;
    struct socket* socket = server_socket_accept(ss);
    struct session* session = malloc(sizeof(struct session));
    if(session == 0) abort();
    session->socket = socket;
    session->mutex = mutex;
    session->games = games;
    thread_start(start_session, session);
  }
  return 0;
}
