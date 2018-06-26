#include "bool.h"
#include "malloc.h"
#include "strings.h"
#include "stdlib.h"
#include "sockets.h"

struct bank {
    int user_account_count;
    struct user_account *user_accounts;
    int bank_account_count;
    struct bank_account *bank_accounts;
};

struct user_account {
    struct user_account *next;
    char *user_name;
    char *password;
    int is_teller;
    char *real_name;
};

struct bank_account {
    struct bank_account *next;
    char *id;
    struct user_account *owner;
    int balance;
    int transaction_count;
    struct transaction *transactions;
};

struct transaction {
    struct transaction *next;
    char *counterparty_bank_account_id;
    int amount;
    char *comment;
};

/*@
predicate transactions(struct transaction *transaction, int count)
    requires
        transaction == 0 ? count == 0 :
            malloc_block_transaction(transaction)
            &*& transaction->next |-> ?next &*& transactions(next, count - 1)
            &*& transaction->counterparty_bank_account_id |-> ?counterparty_id &*& string1(counterparty_id)
            &*& transaction->amount |-> _
            &*& transaction->comment |-> ?comment &*& string1(comment);

predicate bank_accounts(struct bank_account *bankAccount, int count)
    requires
        bankAccount == 0 ? count == 0 :
            malloc_block_bank_account(bankAccount)
            &*& bankAccount->next |-> ?next &*& bank_accounts(next, count - 1)
            &*& bankAccount->id |-> ?id &*& string1(id)
            &*& bankAccount->owner |-> _
            &*& bankAccount->balance |-> _
            &*& bankAccount->transaction_count |-> ?transactionCount
            &*& bankAccount->transactions |-> ?transactions &*& transactions(transactions, transactionCount);

predicate user_accounts(struct user_account *userAccount, int count)
    requires
        userAccount == 0 ? count == 0 :
            malloc_block_user_account(userAccount)
            &*& userAccount->next |-> ?next &*& user_accounts(next, count - 1)
            &*& userAccount->user_name |-> ?userName &*& string1(userName)
            &*& userAccount->password |-> ?password &*& string1(password)
            &*& userAccount->is_teller |-> _
            &*& userAccount->real_name |-> ?realName &*& string1(realName);
@*/
            
char *string_copy(char *string)
    //@ requires string1(string);
    //@ ensures string1(string) &*& string1(result);
{
    char *copy = strdup(string);
    if (copy == 0) {
        abort();
    }
    return copy;
}

bool register_transaction(struct socket *socket, struct bank_account *bankAccounts, char *fromId, char *toId, int amount, char *comment, struct user_account *originator)
    /*@ requires
            socket(socket) &*& bank_accounts(bankAccounts, ?count)
            &*& string1(fromId)
            &*& string1(toId)
            &*& string1(comment);
    @*/
    /*@ ensures
            socket(socket) &*& bank_accounts(bankAccounts, count)
            &*& string1(fromId)
            &*& string1(toId)
            &*& string1(comment);
    @*/
{
    if (bankAccounts == 0) {
        socket_write_string(socket, fromId);
        socket_write_string_literal(socket, ": No such bank account.\r\n");
        return false;
    } else {
        //@ open bank_accounts(bankAccounts, count);
        int cmp = strcmp(bankAccounts->id, fromId);
        if (cmp == 0) {
            if (amount < 0 && bankAccounts->owner != originator) {
                socket_write_string_literal(socket, "You do not own this account.\r\n");
                //@ close bank_accounts(bankAccounts, count);
                return false;
            } else {
                if (bankAccounts->balance + amount < 0) {
                    socket_write_string_literal(socket, "You have insufficient funds available on this account.\r\n");
                    //@ close bank_accounts(bankAccounts, count);
                    return false;
                } else {
                    struct transaction *transaction = malloc(sizeof(struct transaction));
                    if (transaction == 0) {
                        abort();
                    }
                    int txCount = bankAccounts->transaction_count;
                    bankAccounts->transaction_count = txCount + 1;
                    transaction->next = bankAccounts->transactions;
                    char *toIdCopy = string_copy(toId);
                    transaction->counterparty_bank_account_id = toIdCopy;
                    transaction->amount = amount;
                    char *commentCopy = string_copy(comment);
                    transaction->comment = commentCopy;
                    bankAccounts->transactions = transaction;
                    bankAccounts->balance = bankAccounts->balance + amount;
                    //@ close transactions(transaction, txCount + 1);
                    //@ close bank_accounts(bankAccounts, count);
                    return true;
                }
            }
        } else {
            bool result = register_transaction(socket, bankAccounts->next, fromId, toId, amount, comment, originator);
            //@ close bank_accounts(bankAccounts, count);
            return result;
        }
    }
}

void socket_write_transactions_helper2(struct socket *socket, int count, struct transaction *transactions)
    //@ requires socket(socket) &*& transactions(transactions, count);
    //@ ensures socket(socket) &*& transactions(transactions, count);
{
    if (0 < count) {
        //@ open transactions(transactions, count);
        if (transactions->amount < 0) {
            socket_write_string_literal(socket, "Transfer of ");
            socket_write_integer(socket, 0 - transactions->amount);
            socket_write_string_literal(socket, " to ");
            socket_write_string(socket, transactions->counterparty_bank_account_id);
            socket_write_string_literal(socket, " with comment ");
            socket_write_string(socket, transactions->comment);
            socket_write_string_literal(socket, "\r\n");
        } else {
            socket_write_string_literal(socket, "Transfer of ");
            socket_write_integer(socket, transactions->amount);
            socket_write_string_literal(socket, " from ");
            socket_write_string(socket, transactions->counterparty_bank_account_id);
            socket_write_string_literal(socket, " with comment ");
            socket_write_string(socket, transactions->comment);
            socket_write_string_literal(socket, "\r\n");
        }
        socket_write_transactions_helper2(socket, count - 1, transactions->next);
        //@ close transactions(transactions, count);
    }
}

void socket_write_transactions_helper(struct socket *socket, int index, struct bank_account *bankAccounts, struct user_account *userAccount)
    //@ requires socket(socket) &*& bank_accounts(bankAccounts, ?count);
    //@ ensures socket(socket) &*& bank_accounts(bankAccounts, count);
{
    if (bankAccounts != 0) {
        //@ open bank_accounts(bankAccounts, count);
        if (bankAccounts->owner == userAccount) {
            if (index == 0) {
                socket_write_transactions_helper2(socket, bankAccounts->transaction_count, bankAccounts->transactions);
            } else {
                socket_write_transactions_helper(socket, index - 1, bankAccounts->next, userAccount);
            }
        } else {
            socket_write_transactions_helper(socket, index, bankAccounts->next, userAccount);
        }
        //@ close bank_accounts(bankAccounts, count);
    }
}

void socket_write_bank_accounts_helper(struct socket *socket, int i, int count, struct bank_account *bankAccounts, struct user_account *userAccount)
    //@ requires socket(socket) &*& bank_accounts(bankAccounts, count);
    //@ ensures socket(socket) &*& bank_accounts(bankAccounts, count);
{
    if (0 < count) {
        //@ open bank_accounts(bankAccounts, count);
        if (bankAccounts->owner == userAccount) {
            socket_write_integer(socket, i);
            socket_write_string_literal(socket, ". Id: ");
            socket_write_string(socket, bankAccounts->id);
            socket_write_string_literal(socket, "; Balance: ");
            socket_write_integer(socket, bankAccounts->balance);
            socket_write_string_literal(socket, ".\r\n");
            socket_write_bank_accounts_helper(socket, i + 1, count - 1, bankAccounts->next, userAccount);
        } else {
            socket_write_bank_accounts_helper(socket, i, count - 1, bankAccounts->next, userAccount);
        }
        //@ close bank_accounts(bankAccounts, count);
    }
}

struct user_account *lookup_user_account(int count, struct user_account *userAccounts, char *userName)
    //@ requires user_accounts(userAccounts, count) &*& string1(userName);
    //@ ensures user_accounts(userAccounts, count) &*& string1(userName);
{
    if (count == 0) {
        return 0;
    } else {
        //@ open user_accounts(userAccounts, count);
        int cmp = strcmp(userAccounts->user_name, userName);
        if (cmp == 0) {
            //@ close user_accounts(userAccounts, count);
            return userAccounts;
        } else {
            struct user_account *account = lookup_user_account(count - 1, userAccounts->next, userName);
            //@ close user_accounts(userAccounts, count);
            return account;
        }
    }
}

struct authenticate_result {
    struct user_account *user_account;
    int is_teller;
    char *real_name;
};

struct authenticate_result *authenticate_user(struct user_account *userAccounts, char *userName, char *password)
    //@ requires user_accounts(userAccounts, ?count) &*& string1(userName) &*& string1(password);
    /*@ ensures
            user_accounts(userAccounts, count) &*& string1(userName) &*& string1(password)
            &*& (result == 0 ? true :
                     malloc_block_authenticate_result(result)
                     &*& result->user_account |-> _
                     &*& result->is_teller |-> _
                     &*& result->real_name |-> ?realName &*& string1(realName));
    @*/
{
    if (userAccounts == 0) {
        return 0;
    } else {
        //@ open user_accounts(userAccounts, count);
        int userAccountCmp = strcmp(userAccounts->user_name, userName);
        if (userAccountCmp == 0) {
            int passwordCmp = strcmp(userAccounts->password, password);
            if (passwordCmp == 0) {
                struct authenticate_result *result = malloc(sizeof(struct authenticate_result));
                if (result == 0) {
                    abort();
                }
                result->user_account = userAccounts;
                result->is_teller = userAccounts->is_teller;
                char *realNameCopy = string_copy(userAccounts->real_name);
                result->real_name = realNameCopy;
                //@ close user_accounts(userAccounts, count);
                return result;
            } else {
                //@ close user_accounts(userAccounts, count);
                return 0;
            }
        } else {
            struct authenticate_result *result = authenticate_user(userAccounts->next, userName, password);
            //@ close user_accounts(userAccounts, count);
            return result;
        }
    }
}

int socket_read_nonneg_integer_helper(struct socket *socket)
    //@ requires socket(socket);
    //@ ensures socket(socket);
{
    char *buffer = socket_read_line(socket, 20);
    if (buffer == 0) {
        return -1;
    } else {
        int value = parse_nonneg_integer(buffer);
        string_dispose(buffer);
        return value;
    }
}

// START toe te voegen code

void dispose_transactions(struct transaction *transactions)
    //@ requires transactions(transactions, _);
    //@ ensures emp;
{
    //@ open transactions(transactions, _);
    if (transactions == 0) {
    } else {
        struct transaction *next = transactions->next;
        string_dispose(transactions->counterparty_bank_account_id);
        string_dispose(transactions->comment);
        free(transactions);
        dispose_transactions(next);
    }
}

struct bank_account *close_bank_account(struct socket *socket, struct bank *bank, struct bank_account *bankAccounts, char *bankAccountId)
    //@ requires socket(socket) &*& bank->bank_account_count |-> ?totalCount0 &*& bank_accounts(bankAccounts, ?restCount0) &*& string1(bankAccountId);
    /*@ ensures
            socket(socket) &*& bank->bank_account_count |-> ?totalCount &*& bank_accounts(result, ?restCount) &*& string1(bankAccountId)
            &*& totalCount - restCount == totalCount0 - restCount0;
        @*/
{
    if (bankAccounts == 0) {
        socket_write_string_literal(socket, "No such bank account.\r\n");
        return 0;
    } else {
        //@ open bank_accounts(bankAccounts, restCount0);
        int strcmpResult = strcmp(bankAccountId, bankAccounts->id);
        if (strcmpResult == 0) {
            struct bank_account *result = bankAccounts->next;
            string_dispose(bankAccounts->id);
            dispose_transactions(bankAccounts->transactions);
            free(bankAccounts);
            bank->bank_account_count = bank->bank_account_count - 1;
            socket_write_string_literal(socket, "The bank account has been closed.\r\n");
            return result;
        } else {
            struct bank_account *result = close_bank_account(socket, bank, bankAccounts->next, bankAccountId);
            bankAccounts->next = result;
            //@ assert bank_accounts(result, ?n);
            //@ close bank_accounts(bankAccounts, n + 1);
            return bankAccounts;
        }
    }
}

struct bank_account *close_bank_accounts(struct socket *socket, struct bank *bank, struct bank_account *bankAccounts, struct user_account *owner)
    //@ requires socket(socket) &*& bank->bank_account_count |-> ?totalCount0 &*& bank_accounts(bankAccounts, ?restCount0);
    /*@ ensures
            socket(socket) &*& bank->bank_account_count |-> ?totalCount &*& bank_accounts(result, ?restCount)
            &*& totalCount - restCount == totalCount0 - restCount0;
        @*/
{
    if (bankAccounts == 0) {
        return 0;
    } else {
        //@ open bank_accounts(bankAccounts, restCount0);
        if (bankAccounts->owner == owner) {
            socket_write_string_literal(socket, "Closing bank account ");
            socket_write_string(socket, bankAccounts->id);
            socket_write_string_literal(socket, "...\r\n");
            struct bank_account *next = bankAccounts->next;
            string_dispose(bankAccounts->id);
            dispose_transactions(bankAccounts->transactions);
            free(bankAccounts);
            bank->bank_account_count = bank->bank_account_count - 1;
            bankAccounts = next;
            struct bank_account *result = close_bank_accounts(socket, bank, next, owner);
            return result;
        } else {
            struct bank_account *result = close_bank_accounts(socket, bank, bankAccounts->next, owner);
            bankAccounts->next = result;
            //@ assert bank_accounts(result, ?n);
            //@ close bank_accounts(bankAccounts, n + 1);
            return bankAccounts;
        }
    }
}

struct user_account *close_user_account(struct socket *socket, struct bank *bank, struct user_account *userAccounts, struct user_account *target)
    //@ requires socket(socket) &*& bank->user_account_count |-> ?totalCount0 &*& user_accounts(userAccounts, ?restCount0);
    //@ ensures socket(socket) &*& bank->user_account_count |-> ?totalCount &*& user_accounts(result, ?restCount) &*& totalCount - restCount == totalCount0 - restCount0;
{
    if (userAccounts == 0) {
        return 0;
    } else {
        //@ open user_accounts(userAccounts, restCount0);
        if (userAccounts == target) {
            struct user_account *next = target->next;
            string_dispose(target->user_name);
            string_dispose(target->password);
            string_dispose(target->real_name);
            free(target);
            bank->user_account_count = bank->user_account_count - 1;
            socket_write_string_literal(socket, "The user account has been closed.\r\n");
            return next;
        } else {
            struct user_account *result = close_user_account(socket, bank, userAccounts->next, target);
            userAccounts->next = result;
            //@ assert user_accounts(result, ?n);
            //@ close user_accounts(userAccounts, n + 1);
            return userAccounts;
        }
    }
}

// EINDE toe te voegen code

void handle_connection(struct bank *bank, struct socket *socket, struct user_account *userAccount, int isTeller, char *realName)
    /*@ requires
            bank->user_account_count |-> ?_userAccountCount &*& bank->user_accounts |-> ?_userAccounts &*& user_accounts(_userAccounts, _userAccountCount)
            &*& bank->bank_account_count |-> ?_bankAccountCount &*& bank->bank_accounts |-> ?_bankAccounts &*& bank_accounts(_bankAccounts, _bankAccountCount)
            &*& socket(socket)
            &*& string1(realName);
    @*/
    /*@ ensures
            bank->user_account_count |-> ?_userAccountCount2 &*& bank->user_accounts |-> ?_userAccounts2 &*& user_accounts(_userAccounts2, _userAccountCount2)
            &*& bank->bank_account_count |-> ?_bankAccountCount2 &*& bank->bank_accounts |-> ?_bankAccounts2 &*& bank_accounts(_bankAccounts2, _bankAccountCount2)
            &*& socket(socket)
            &*& string1(realName);
    @*/
{
    socket_write_string_literal(socket, "Welcome, ");
    socket_write_string(socket, realName);
    socket_write_string_literal(socket, ".\r\n");
    bool done = false;
    while (!done)
        /*@ invariant
                bank->user_account_count |-> ?_userAccountCount0 &*& bank->user_accounts |-> ?_userAccounts0 &*& user_accounts(_userAccounts0, _userAccountCount0)
                &*& bank->bank_account_count |-> ?_bankAccountCount0 &*& bank->bank_accounts |-> ?_bankAccounts0 &*& bank_accounts(_bankAccounts0, _bankAccountCount0)
                &*& socket(socket);
        @*/
    {
        if (isTeller != 0) {
            socket_write_string_literal(socket, "Teller Menu\r\n1. Add user account\r\n2. Add bank account\r\n3. Close bank account\r\n4. Close user account\r\n0. Done\r\n");
            int choice = socket_read_nonneg_integer_helper(socket);
            if (choice == 1) {
                socket_write_string_literal(socket, "Enter user name for new account:\r\n");
                char *userName = socket_read_line(socket, 30);
                if (userName != 0) {
                    socket_write_string_literal(socket, "Enter password for new account:\r\n");
                    char *password = socket_read_line(socket, 30);
                    if (password != 0) {
                        socket_write_string_literal(socket, "Enter real name for new account:\r\n");
                        char *newAccountRealName = socket_read_line(socket, 30);
                        if (newAccountRealName != 0) {
                            struct user_account *newAccount = malloc(sizeof(struct user_account));
                            if (newAccount == 0) {
                                abort();
                            }
                            newAccount->user_name = userName;
                            newAccount->password = password;
                            newAccount->is_teller = 0;
                            newAccount->real_name = newAccountRealName;
                            newAccount->next = bank->user_accounts;
                            bank->user_accounts = newAccount;
                            bank->user_account_count = bank->user_account_count + 1;
                            //@ close user_accounts(newAccount, bank->user_account_count);
                            socket_write_string_literal(socket, "The new user account has been added.\r\n");
                        } else {
                            string_dispose(password);
                            string_dispose(userName);
                            done = true;
                        }
                    } else {
                        string_dispose(userName);
                        done = true;
                    }
                } else {
                    done = true;
                }
            } else {
                if (choice == 2) {
                    socket_write_string_literal(socket, "Please enter an ID for the new account.\r\n");
                    char *id = socket_read_line(socket, 20);
                    if (id != 0) {
                        socket_write_string_literal(socket, "Please enter the user name of the owner of the new account.\r\n");
                        char *ownerUserName = socket_read_line(socket, 30);
                        if (ownerUserName != 0) {
                            struct user_account *ownerAccount = lookup_user_account(bank->user_account_count, bank->user_accounts, ownerUserName);
                            string_dispose(ownerUserName);
                            if (ownerAccount == 0) {
                                socket_write_string_literal(socket, "No such user.\r\n");
                                string_dispose(id);
                            } else {
                                socket_write_string_literal(socket, "Please enter the amount of the initial deposit.\r\n");
                                int amount = socket_read_nonneg_integer_helper(socket);
                                if (amount < 0) {
                                    string_dispose(id);
                                    done = true;
                                } else {
                                    struct bank_account *account = malloc(sizeof(struct bank_account));
                                    if (account == 0) {
                                        abort();
                                    }
                                    account->next = bank->bank_accounts;
                                    account->id = id;
                                    account->owner = ownerAccount;
                                    account->balance = amount;
                                    account->transaction_count = 0;
                                    account->transactions = 0;
                                    //@ close transactions(0, 0);
                                    bank->bank_accounts = account;
                                    bank->bank_account_count = bank->bank_account_count + 1;
                                    //@ close bank_accounts(account, bank->bank_account_count);
                                    socket_write_string_literal(socket, "The new account has been added.\r\n");
                                }
                            }
                        } else {
                            string_dispose(id);
                            done = true;
                        }
                    } else {
                        done = true;
                    }
                } else {
                    if (choice == 3) {
                        // START toe te voegen code
                        socket_write_string_literal(socket, "Please enter the ID of the bank account being closed.\r\n");
                        char *id = socket_read_line(socket, 20);
                        if (id != 0) {
                            struct bank_account *bankAccounts = bank->bank_accounts;
                            bankAccounts = close_bank_account(socket, bank, bankAccounts, id);
                            bank->bank_accounts = bankAccounts;
                            string_dispose(id);
                        } else {
                            done = true;
                        }
                        // EINDE toe te voegen code
                    } else {
                        if (choice  == 4) {
                            // START toe te voegen code
                            socket_write_string_literal(socket, "Please enter the user name of the user account being closed.\r\n");
                            char *userName = socket_read_line(socket, 30);
                            if (userName != 0) {
                                struct user_account *target = lookup_user_account(bank->user_account_count, bank->user_accounts, userName);
                                string_dispose(userName);
                                if (target == 0) {
                                    socket_write_string_literal(socket, "No such user account.\r\n");
                                } else {
                                    struct bank_account *bankAccounts = bank->bank_accounts;
                                    bankAccounts = close_bank_accounts(socket, bank, bankAccounts, target);
                                    bank->bank_accounts = bankAccounts;
                                    struct user_account *userAccounts = bank->user_accounts;
                                    userAccounts = close_user_account(socket, bank, userAccounts, target);
                                    bank->user_accounts = userAccounts;
                                }
                            } else {
                                done = true;
                            }
                            // EINDE toe te voegen code
                        } else {
                            done = true;
                        }
                    }
                }
            }
        } else {
            socket_write_string_literal(socket, "Client menu\r\n1. View accounts\r\n2. Perform wire transfer\r\n0. Done\r\n");
            int choice = socket_read_nonneg_integer_helper(socket);
            if (choice == 1) {
                socket_write_string_literal(socket, "Accounts:\r\n");
                socket_write_bank_accounts_helper(socket, 1, bank->bank_account_count, bank->bank_accounts, userAccount);
                socket_write_string_literal(socket, "Enter account index to view transactions:\r\n");
                int index = socket_read_nonneg_integer_helper(socket);
                if (index < 0) {
                    done = true;
                } else {
                    if (1 <= index) {
                        socket_write_transactions_helper(socket, index - 1, bank->bank_accounts, userAccount);
                    }
                }
            } else {
               if (choice == 2) {
                   socket_write_string_literal(socket, "Please enter the account id of your account:\r\n");
                   char *fromId = socket_read_line(socket, 30);
                   if (fromId != 0) {
                       socket_write_string_literal(socket, "Please enter the target account id:\r\n");
                       char *toId = socket_read_line(socket, 30);
                       if (toId != 0) {
                           socket_write_string_literal(socket, "Please enter the amount:\r\n");
                           int amount = socket_read_nonneg_integer_helper(socket);
                           if (0 <= amount) {
                               socket_write_string_literal(socket, "Please enter the comment:\r\n");
                               char *comment = socket_read_line(socket, 100);
                               if (comment != 0) {
                                   bool result = register_transaction(socket, bank->bank_accounts, fromId, toId, 0 - amount, comment, userAccount);
                                   if (result) {
                                       register_transaction(socket, bank->bank_accounts, toId, fromId, amount, comment, 0);
                                   }
                                   string_dispose(comment);
                               } else {
                                   done = true;
                               }
                           } else {
                               done = true;
                           }
                           string_dispose(toId);
                       } else {
                           done = true;
                       }
                       string_dispose(fromId);
                   } else {
                       done = true;
                   }
               } else {
                   done = true;
               }
           }
       }
   }
}

void add_root_account(struct bank *bank)
    //@ requires bank->user_account_count |-> 0 &*& bank->user_accounts |-> ?userAccounts0 &*& user_accounts(userAccounts0, 0);
    //@ ensures bank->user_account_count |-> 1 &*& bank->user_accounts |-> ?userAccounts &*& user_accounts(userAccounts, 1);
{
    char *rootUserName = create_string("root");
    char *rootPassword = create_string("root");
    char *rootRealName = create_string("root");
    struct user_account *rootAccount = malloc(sizeof(struct user_account));
    if (rootAccount == 0) {
        abort();
    }
    rootAccount->next = bank->user_accounts;
    rootAccount->user_name = rootUserName;
    rootAccount->password = rootPassword;
    rootAccount->is_teller = 1;
    rootAccount->real_name = rootRealName;
    bank->user_accounts = rootAccount;
    bank->user_account_count = 1;
    //@ close user_accounts(rootAccount, 1);
}

int main() //@ : main
    //@ requires emp;
    //@ ensures emp;
{
    struct bank *bank = malloc(sizeof(struct bank));
    if (bank == 0) {
        abort();
    }
    bank->user_account_count = 0;
    bank->user_accounts = 0;
    //@ close user_accounts(0, 0);
    bank->bank_account_count = 0;
    bank->bank_accounts = 0;
    //@ close bank_accounts(0, 0);

    add_root_account(bank);

    struct server_socket *serverSocket = create_server_socket(12345);

    while (true)
        /*@ invariant
                server_socket(serverSocket)
                &*& bank->user_account_count |-> ?_userAccountCount &*& bank->user_accounts |-> ?_userAccounts &*& user_accounts(_userAccounts, _userAccountCount)
                &*& bank->bank_account_count |-> ?_bankAccountCount &*& bank->bank_accounts |-> ?_bankAccounts &*& bank_accounts(_bankAccounts, _bankAccountCount);
        @*/
    {
        struct socket *socket = server_socket_accept(serverSocket);

        socket_write_string_literal(socket, "Welcome to Home Banking.\r\n");
        socket_write_string_literal(socket, "Please enter your username.\r\n");
        char *userName = socket_read_line(socket, 30);
        if (userName != 0) {
            socket_write_string_literal(socket, "Please enter your password.\r\n");
            char *password = socket_read_line(socket, 30);
            if (password != 0) {
                struct authenticate_result *result = authenticate_user(bank->user_accounts, userName, password);
                if (result == 0) {
                    socket_write_string_literal(socket, "Incorrect username, password combination. Closing the connection.\r\n");
                } else {
                    handle_connection(bank, socket, result->user_account, result->is_teller, result->real_name);
                    string_dispose(result->real_name);
                    free(result);
                }
                string_dispose(password);
            }
            string_dispose(userName);
        }

        socket_close(socket);
    }
}
