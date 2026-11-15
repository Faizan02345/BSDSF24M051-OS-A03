#include "shell.h"

#include <fcntl.h>
#include <errno.h>
#include <sys/wait.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#define MAX_JOBS 20

typedef struct {
    int job_id;
    pid_t pids[MAXARGS];
    int process_count;
    char command[MAX_LEN];
    int active;
} Job;


static Job job_list[MAX_JOBS];
static int next_job_id = 1;

/* Shell-local variables */
#define MAX_VARIABLES 50

typedef struct {
    char name[ARGLEN];
    char value[MAX_LEN];
} ShellVariable;

static ShellVariable variables[MAX_VARIABLES];
static int variable_count = 0;

static int valid_variable_name(const char *name, size_t length) {
    if (length == 0 || length >= ARGLEN) {
        return 0;
    }

    if (!(isalpha((unsigned char)name[0]) || name[0] == '_')) {
        return 0;
    }

    for (size_t i = 1; i < length; i++) {
        if (!(isalnum((unsigned char)name[i]) || name[i] == '_')) {
            return 0;
        }
    }

    return 1;
}

static int find_variable(const char *name) {
    for (int i = 0; i < variable_count; i++) {
        if (strcmp(variables[i].name, name) == 0) {
            return i;
        }
    }
    return -1;
}

static void set_variable(const char *name, const char *value) {
    int index = find_variable(name);

    if (index == -1) {
        if (variable_count >= MAX_VARIABLES) {
            fprintf(stderr, "Variable table is full.\n");
            return;
        }
        index = variable_count++;
        snprintf(variables[index].name,
                 sizeof(variables[index].name), "%s", name);
    }

    snprintf(variables[index].value,
             sizeof(variables[index].value), "%s", value);
}

static int handle_assignment(char **arglist) {
    if (arglist[0] == NULL || arglist[1] != NULL) {
        return 0;
    }

    char *equals = strchr(arglist[0], '=');
    if (equals == NULL) {
        return 0;
    }

    size_t name_length = (size_t)(equals - arglist[0]);
    if (!valid_variable_name(arglist[0], name_length)) {
        return 0;
    }

    char name[ARGLEN];
    memcpy(name, arglist[0], name_length);
    name[name_length] = '\0';

    set_variable(name, equals + 1);
    return 1;
}

static const char *get_variable_value(const char *name) {
    int index = find_variable(name);
    return index >= 0 ? variables[index].value : "";
}

/* Expand $NAME and ${NAME} in each argument before command execution. */
static void expand_one_argument(const char *source,
                                char *destination, size_t capacity) {
    size_t out = 0;

    for (size_t i = 0; source[i] != '\0' && out + 1 < capacity;) {
        if (source[i] != '$') {
            destination[out++] = source[i++];
            continue;
        }

        size_t name_start;
        size_t name_end;
        int braced = 0;

        if (source[i + 1] == '{') {
            braced = 1;
            name_start = i + 2;
            name_end = name_start;
            while (source[name_end] != '\0' && source[name_end] != '}') {
                name_end++;
            }
            if (source[name_end] != '}') {
                destination[out++] = source[i++];
                continue;
            }
        } else {
            name_start = i + 1;
            name_end = name_start;
            while (isalnum((unsigned char)source[name_end]) ||
                   source[name_end] == '_') {
                name_end++;
            }
            if (name_end == name_start) {
                destination[out++] = source[i++];
                continue;
            }
        }

        size_t name_length = name_end - name_start;
        if (name_length > 0 && name_length < ARGLEN) {
            char name[ARGLEN];
            memcpy(name, source + name_start, name_length);
            name[name_length] = '\0';

            const char *value = get_variable_value(name);
            while (*value != '\0' && out + 1 < capacity) {
                destination[out++] = *value++;
            }
        }

        i = braced ? name_end + 1 : name_end;
    }

    destination[out] = '\0';
}

static void expand_arguments(char **source, char **destination,
                             char storage[MAXARGS][MAX_LEN]) {
    int i = 0;

    while (source[i] != NULL && i < MAXARGS) {
        expand_one_argument(source[i], storage[i], MAX_LEN);
        destination[i] = storage[i];
        i++;
    }

    destination[i] = NULL;
}

static void reap_background_jobs(void);
static void show_jobs(void);
static void add_job(pid_t pids[], int count, const char *command);
static int execute_single(char **arglist, int background,
                          const char *command);
static int execute_pipeline(char **arglist, int background,
                            const char *command);

/* Add a background job to the job table */
static void add_job(pid_t pids[], int count, const char *command) {
    for (int i = 0; i < MAX_JOBS; i++) {
        if (!job_list[i].active) {
            job_list[i].job_id = next_job_id++;
            job_list[i].process_count = count;
            job_list[i].active = 1;

            for (int j = 0; j < count; j++) {
                job_list[i].pids[j] = pids[j];
            }

            snprintf(job_list[i].command, MAX_LEN, "%s", command);

            printf("[%d] %d Running %s\n",
                   job_list[i].job_id, pids[0], command);
            fflush(stdout);
            return;
        }
    }

    fprintf(stderr, "Maximum background jobs reached.\n");

    for (int i = 0; i < count; i++) {
        waitpid(pids[i], NULL, 0);
    }
}

/* Reap completed background processes without blocking */
static void reap_background_jobs(void) {
    int status;
    pid_t finished_pid;

    /*
     * -1 means wait for any child process.
     * WNOHANG makes waitpid non-blocking.
     */
    while (1) {
        finished_pid = waitpid(-1, &status, WNOHANG);

        if (finished_pid > 0) {
            for (int i = 0; i < MAX_JOBS; i++) {
                if (!job_list[i].active) {
                    continue;
                }

                for (int j = 0; j < job_list[i].process_count; j++) {
                    if (job_list[i].pids[j] == finished_pid) {
                        job_list[i].pids[j] = -1;
                        break;
                    }
                }
            }
        }
        else if (finished_pid == 0) {
            break;
        }
        else {
            if (errno == EINTR) {
                continue;
            }

            break;
        }
    }

    /* Check which jobs have completed */
    for (int i = 0; i < MAX_JOBS; i++) {
        if (!job_list[i].active) {
            continue;
        }

        int completed = 1;

        for (int j = 0; j < job_list[i].process_count; j++) {
            if (job_list[i].pids[j] > 0) {
                completed = 0;
                break;
            }
        }

        if (completed) {
            printf("[%d] Done %s\n",
                   job_list[i].job_id,
                   job_list[i].command);

            job_list[i].active = 0;
        }
    }
}

/* Display background jobs */
static void show_jobs(void) {
    reap_background_jobs();

    int found = 0;

    for (int i = 0; i < MAX_JOBS; i++) {
        if (job_list[i].active) {
            found = 1;

            printf("[%d] Running %d %s\n",
                   job_list[i].job_id,
                   job_list[i].pids[0],
                   job_list[i].command);
        }
    }

    if (!found) {
        printf("No background jobs.\n");
    }
}

/* Execute built-in commands */
static int execute_builtin(char **arglist) {

    if (strcmp(arglist[0], "exit") == 0) {
        printf("Exiting shell...\n");
        exit(0);
    }

    if (strcmp(arglist[0], "cd") == 0) {
        char *path = arglist[1];

        if (path == NULL) {
            path = getenv("HOME");
        }

        if (path == NULL || chdir(path) != 0) {
            perror("cd");
            return 1;
        }

        return 0;
    }

    if (strcmp(arglist[0], "help") == 0) {
        printf("\nBuilt-in commands:\n");
        printf("  exit     - Exit the shell\n");
        printf("  cd       - Change directory\n");
        printf("  help     - Display help information\n");
        printf("  jobs     - Display background jobs\n");
        printf("  history  - Display command history\n");
        printf("  set      - Display shell variables\n");
        printf("  NAME=value - Create or update a shell variable\n");
        printf("  ;        - Execute commands sequentially\n");
        printf("  &        - Execute command in background\n\n");

        return 0;
    }

    if (strcmp(arglist[0], "jobs") == 0) {
        show_jobs();
        return 0;
    }

    if (strcmp(arglist[0], "history") == 0) {
        show_history();
        return 0;
    }

    if (strcmp(arglist[0], "set") == 0) {
        for (int i = 0; i < variable_count; i++) {
            printf("%s=%s\n",
                   variables[i].name, variables[i].value);
        }
        return 0;
    }

    return -1;
}

/* Execute a command with input/output descriptors */
static void execute_command(char **args, int input_fd, int output_fd) {

    if (input_fd != STDIN_FILENO) {
        if (dup2(input_fd, STDIN_FILENO) == -1) {
            perror("dup2 input");
            _exit(1);
        }
    }

    if (output_fd != STDOUT_FILENO) {
        if (dup2(output_fd, STDOUT_FILENO) == -1) {
            perror("dup2 output");
            _exit(1);
        }
    }

    if (input_fd != STDIN_FILENO) {
        close(input_fd);
    }

    if (output_fd != STDOUT_FILENO) {
        close(output_fd);
    }

    execvp(args[0], args);

    perror("Command execution failed");
    _exit(1);
}

/* Execute pipelines and redirections */
static int execute_pipeline(char **arglist, int background,
                            const char *command) {

    char *commands[MAXARGS][MAXARGS + 1] = {0};
    char *input_files[MAXARGS] = {0};
    char *output_files[MAXARGS] = {0};

    int command_count = 1;
    int argument_count = 0;

    for (int i = 0; arglist[i] != NULL; i++) {

        if (strcmp(arglist[i], "|") == 0) {

            if (argument_count == 0 || command_count >= MAXARGS) {
                fprintf(stderr, "Invalid pipe syntax\n");
                return 1;
            }

            commands[command_count - 1][argument_count] = NULL;
            command_count++;
            argument_count = 0;
        }

        else if (strcmp(arglist[i], "<") == 0) {

            if (arglist[i + 1] == NULL ||
                input_files[command_count - 1] != NULL) {
                fprintf(stderr, "Invalid input redirection\n");
                return 1;
            }

            input_files[command_count - 1] = arglist[++i];
        }

        else if (strcmp(arglist[i], ">") == 0) {

            if (arglist[i + 1] == NULL ||
                output_files[command_count - 1] != NULL) {
                fprintf(stderr, "Invalid output redirection\n");
                return 1;
            }

            output_files[command_count - 1] = arglist[++i];
        }

        else {
            if (argument_count >= MAXARGS) {
                fprintf(stderr, "Too many arguments\n");
                return 1;
            }

            commands[command_count - 1][argument_count++] = arglist[i];
        }
    }

    if (argument_count == 0) {
        fprintf(stderr, "Invalid command syntax\n");
        return 1;
    }

    commands[command_count - 1][argument_count] = NULL;

    for (int i = 0; i < command_count; i++) {
        if (commands[i][0] == NULL) {
            fprintf(stderr, "Missing command\n");
            return 1;
        }
    }

    int previous_read = STDIN_FILENO;
    pid_t pids[MAXARGS];
    int created = 0;

    for (int i = 0; i < command_count; i++) {

        int pipe_fd[2] = {-1, -1};

        if (i < command_count - 1) {
            if (pipe(pipe_fd) == -1) {
                perror("pipe");
                break;
            }
        }

        pid_t pid = fork();

        if (pid == -1) {
            perror("fork");

            if (pipe_fd[0] != -1) close(pipe_fd[0]);
            if (pipe_fd[1] != -1) close(pipe_fd[1]);

            break;
        }

        if (pid == 0) {

            int input_fd = previous_read;
            int output_fd = (i < command_count - 1)
                            ? pipe_fd[1] : STDOUT_FILENO;

            if (input_files[i] != NULL) {
                input_fd = open(input_files[i], O_RDONLY);

                if (input_fd == -1) {
                    perror("input file");
                    _exit(1);
                }

                if (previous_read != STDIN_FILENO) {
                    close(previous_read);
                }
            }

            if (output_files[i] != NULL) {
                output_fd = open(output_files[i],
                                  O_WRONLY | O_CREAT | O_TRUNC,
                                  0644);

                if (output_fd == -1) {
                    perror("output file");
                    _exit(1);
                }

                if (pipe_fd[1] != -1) {
                    close(pipe_fd[1]);
                }
            }

            if (pipe_fd[0] != -1) {
                close(pipe_fd[0]);
            }

            execute_command(commands[i], input_fd, output_fd);
        }

        pids[created++] = pid;

        if (previous_read != STDIN_FILENO) {
            close(previous_read);
        }

        if (pipe_fd[1] != -1) {
            close(pipe_fd[1]);
        }

        previous_read = pipe_fd[0];
    }

    if (previous_read != STDIN_FILENO && previous_read != -1) {
        close(previous_read);
    }

    if (created == 0) {
        return 1;
    }

    if (background) {
        add_job(pids, created, command);
        return 0;
    }

    int status = 0;

    for (int i = 0; i < created; i++) {
        int child_status;

        if (waitpid(pids[i], &child_status, 0) == -1) {
            perror("waitpid");
            status = 1;
        }
        else if (i == created - 1) {
            status = WIFEXITED(child_status)
                     ? WEXITSTATUS(child_status) : 1;
        }
    }

    return status;
}

/* Execute one command */
static int execute_single(char **arglist, int background,
                          const char *command) {

    if (arglist == NULL || arglist[0] == NULL) {
        return 0;
    }

    int has_operator = 0;

    for (int i = 0; arglist[i] != NULL; i++) {
        if (strcmp(arglist[i], "<") == 0 ||
            strcmp(arglist[i], ">") == 0 ||
            strcmp(arglist[i], "|") == 0) {
            has_operator = 1;
            break;
        }
    }

    if (has_operator) {
        return execute_pipeline(arglist, background, command);
    }

    /* Variable assignments must run in the shell process, not a child. */
    if (handle_assignment(arglist)) {
        return 0;
    }

    if (!background) {
        int result = execute_builtin(arglist);

        if (result != -1) {
            return result;
        }
    }

    pid_t pid = fork();

    if (pid == -1) {
        perror("fork");
        return 1;
    }

    if (pid == 0) {
        if (background) {
            int result = execute_builtin(arglist);

            if (result != -1) {
                _exit(result);
            }
        }

        execvp(arglist[0], arglist);
        perror("Command execution failed");
        _exit(1);
    }

    if (background) {
        add_job(&pid, 1, command);
        return 0;
    }

    int status;

    if (waitpid(pid, &status, 0) == -1) {
        perror("waitpid");
        return 1;
    }

    return WIFEXITED(status) ? WEXITSTATUS(status) : 1;
}

/* Build the complete command text for job display */
static void build_command(char *buffer, size_t size,
                          char **arglist, int start, int end) {

    buffer[0] = '\0';
    size_t used = 0;

    for (int i = start; i < end; i++) {
        int written = snprintf(buffer + used, size - used,
                               "%s%s",
                               (i == start) ? "" : " ",
                               arglist[i]);

        if (written < 0 || (size_t)written >= size - used) {
            break;
        }

        used += (size_t)written;
    }
}

/* Main execute function */
int execute(char **arglist) {

    if (arglist == NULL || arglist[0] == NULL) {
        return 0;
    }

    reap_background_jobs();

    int start = 0;
    int status = 0;

    for (int i = 0; ; i++) {

        if (arglist[i] == NULL ||
            strcmp(arglist[i], ";") == 0 ||
            strcmp(arglist[i], "&") == 0) {

            int background = 0;

            if (arglist[i] != NULL &&
                strcmp(arglist[i], "&") == 0) {
                background = 1;
            }

            char command[MAX_LEN];
            build_command(command, sizeof(command), arglist, start, i);

            char *separator = arglist[i];
            arglist[i] = NULL;

            if (start < i) {
                char expanded_storage[MAXARGS][MAX_LEN];
                char *expanded_args[MAXARGS + 1];

                expand_arguments(&arglist[start],
                                 expanded_args,
                                 expanded_storage);

                status = execute_single(expanded_args,
                                        background,
                                        command);
            }

            if (separator == NULL) {
                break;
            }

            arglist[i] = separator;
            start = i + 1;
        }
    }

    reap_background_jobs();

    return status;
}

