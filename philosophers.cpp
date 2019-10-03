/* CSC 2/458: Parallel and Distributed Systems
 * Spring 2019
 * Assignment 2: Drinking Philosophers
 * Author: Soubhik Ghosh (netId: sghosh13)
 */

#include <bits/stdc++.h>
#include <unistd.h>

constexpr int SESSION_COUNT = 20;
constexpr int MAX_PHILOSOPHERS = 100;
constexpr int MAX_FORKS = 500;

/* The diners problem is a special case of the drinkers problem in which every
 * thirsty philosopher needs bottles associated with all its incident edges for all drinking sessions.
 * Hence this solution treats all the bottles as forks but reports drinking instead of eating in the ouput.
 */

class Fork 
{
private:
	int fork_holder;	/* Id of the philosopher holding the fork */
	int rtok_holder;	/* Id of the philosopher holding the request token */
	bool is_dirty = true;	/* Condition of the fork */
	std::mutex m_lockfork;	/* Lock for changing the state of the fork */
	std::pair <int, int> direction;		/* Direction of the edge from first to second */
public:
	void set_edge(int u, int v) {
		/* The token and the dirty fork are initially held by different philisophers sharing the same fork */
		direction = std::make_pair(u, v);
		fork_holder = v;	/* Fork initially held by the philosopher with in-edge */
		rtok_holder = u;
	}

	void swap_edge() {
		direction = std::make_pair(direction.second, direction.first);
	}

	int get_neighbor(int u) {
		return u == direction.first ? direction.second : direction.first;
	}

	bool has_fork(int u) const {
		return fork_holder == u;
	}
	bool has_ftok(int u) const {
		return rtok_holder == u;
	}
	friend class Graph;
};

/* Precedence graph of drinking philosophers representing conflict model */
class Graph
{
public:
	enum DiningState 
	{
		THINKING,
		HUNGRY,
		EATING
	};
private:
	struct Philosopher 
	{
		std::thread philosopher;	/* Instance of a participating philosopher */
		bool visited = false;	/* Used for graph traversal operations */
		int depth = 0;	/* Depth is the maximum number of edges on any path to the philosopher */
		DiningState m_state = HUNGRY;	/* Every philosopher starts a session hungry */
		std::condition_variable m_depthcheck;    /* Used for waiting on precedence */
		std::set<int> incident_forks;	/* Set of all numbered forks shareable by the philosopher */
	} m_list_philosophers[MAX_PHILOSOPHERS];

	int m_num_philosophers;
	int m_num_edges = 0;
	Fork m_fork_list[MAX_FORKS];
	int m_num_sessions = SESSION_COUNT;

	/* Used by the random_r library routine */
	struct random_data buf;
	char statebuf[256];

	/* This function is used to update the depths in the graph after changing direction of edges */
	int update_depths(int id) {
		int curr_depth = 0;
		for (auto const f : m_list_philosophers[id].incident_forks) {
			if (id == m_fork_list[f].direction.second) {
				curr_depth = std::max(curr_depth, 1 + update_depths(m_fork_list[f].direction.first));
			}
		}
		m_list_philosophers[id].depth = curr_depth;
		return curr_depth;
	}
public:
	Graph(int num_sessions = SESSION_COUNT) : m_num_sessions(num_sessions) {
		/* Initialize the seed of the random number generator with the current time
		 * Each eating/thinking session occurs for 1-1000 microseconds
		 */
		if(initstate_r(time(NULL), statebuf, 256, &buf) != 0) {
			std::cerr << "initstate_r failed: " << strerror(errno) << std::endl;	
			exit(EXIT_FAILURE);
		}
	}
	~Graph() {}

	void set_philosophers(int num_philosophers) {
		m_num_philosophers = num_philosophers;
	}

	void add_edge(int u, int v) {
		/* Test for bounded ids */
		if (u < 0 || u >= m_num_philosophers || v < 0 || v >= m_num_philosophers) 
			throw std::string("Sorry, these don't seem to be our philosophers.\nExiting...");

		/* Test for self loops */
		if (u == v)
			throw std::string("Sorry, our philosophers can't completely keep the forks to themselves.\n"
					"Sharing is caring - Remember? Exiting...");

		/* Test for duplicate edges */
		auto it = std::find_if(m_fork_list, m_fork_list + m_num_edges, [u, v](const Fork& f) {
			return (f.direction == std::make_pair(u, v)) || (f.direction == std::make_pair(v, u));
		});

		if (it != m_fork_list + m_num_edges)
			throw std::string("Sorry, the neighbours are allowed to share atmost one fork. \nExiting...");

		/* Initially all the eges are undirected */
		m_fork_list[m_num_edges].set_edge(u, v);
		m_list_philosophers[u].incident_forks.insert(m_num_edges);
		m_list_philosophers[v].incident_forks.insert(m_num_edges);
		m_num_edges++;
	}

	bool is_connected() const {
		/* Note: use this function only after adding all the edges */
		return m_num_edges >= (m_num_philosophers - 1) && m_num_edges <= m_num_philosophers * (m_num_philosophers - 1) / 2;
	}

	void set_DAG() {
		/* Using BFS for converting into directed acyclic graph.
		 * This will intially give the 0th philosopher the highest precedence and only she can start while others wait for her 
		 */
		std::queue<int> Q;
		Q.push(0);
		int id;
		while (!Q.empty()) {
			id = Q.front();
			Q.pop();
			m_list_philosophers[id].visited = true;
			for (auto const f : m_list_philosophers[id].incident_forks) {
				if (id == m_fork_list[f].direction.second &&
					!m_list_philosophers[m_fork_list[f].direction.first].visited) {
					m_fork_list[f].swap_edge();
					std::tie(m_fork_list[f].rtok_holder, m_fork_list[f].fork_holder) = m_fork_list[f].direction;
				}
				if (!m_list_philosophers[m_fork_list[f].direction.second].visited) {
					Q.push(m_fork_list[f].direction.second);
				}
				m_list_philosophers[m_fork_list[f].direction.second].depth =
					std::max(m_list_philosophers[m_fork_list[f].direction.second].depth,
						m_list_philosophers[m_fork_list[f].direction.first].depth + 1);
			}
		}
	}

	/* Function to start the drinking sessions */
	void start() {
		/* Locks for writing to the output and altering the graph */
		std::mutex lockprint, lockgraph;

		std::atomic_bool start(false);
		for (int id = 0; id < m_num_philosophers; id++) {
			m_list_philosophers[id].philosopher = std::thread([&, id]()
			{
				int num_sessions = m_num_sessions;
				int32_t result;

				/* Spinning */
				while (!start.load());

				while (num_sessions-- > 0) {
					/* Start hungry/thirsty */
					m_list_philosophers[id].m_state = HUNGRY;
					
					/* Wait till the philosopher has precedence (depth = 0) */
					{
						std::unique_lock<std::mutex> glocker(lockgraph);
						m_list_philosophers[id].m_depthcheck.wait(glocker, [&](){
							return m_list_philosophers[id].depth == 0;
						});
					}

					/* Get all the clean forks */
					for (auto const f : m_list_philosophers[id].incident_forks) {

						std::lock_guard<std::mutex> flocker(m_fork_list[f].m_lockfork);

						/* Send Request token if no fork and ask neighbour to receive the fork */
						if (m_fork_list[f].has_ftok(id) && !m_fork_list[f].has_fork(id)) {
							/* Send token */
							m_fork_list[f].rtok_holder = m_fork_list[f].get_neighbor(id);
							/* Check if neighbor is not eating and has the request token with dirty spoon */
							if ((m_list_philosophers[m_fork_list[f].rtok_holder].m_state != EATING) &&
								m_fork_list[f].has_ftok(m_fork_list[f].rtok_holder) &&
								m_fork_list[f].is_dirty) {
								/* Get the spoon, cleaned */
								m_fork_list[f].is_dirty = false;
								m_fork_list[f].fork_holder = id;
							}
							/* Continue upon receving clean fork */
						}
						/* Note: No need to check whether a philosopher already has a dirty fork because she won't at this point.
						 * Assume the philosopher needs a fork which she already has and is dirty.
						 * Dirty fork implies the edge is pointing towards the philosopher and her depth is non zero.
						 * Hence she should be waiting for her depth to be zero by spinning but instead she's here,
						 * requesting for the fork which is a contradiction.
						*/
					}

					/* Start Eating/Drinking */
					m_list_philosophers[id].m_state = EATING;
					/* Print an eating/drinking message */
					{
						std::lock_guard<std::mutex> llocker(lockprint);
						std::cout << "philosopher " << id + 1 << " drinking" << std::endl;
					}
					/* Dirty the forks */
					for (auto const f : m_list_philosophers[id].incident_forks) {
						std::lock_guard<std::mutex> flocker(m_fork_list[f].m_lockfork);
						m_fork_list[f].is_dirty = true;
					}

					if (random_r(&buf, &result) != 0) {
						std::lock_guard<std::mutex> llocker(lockprint);
						std::cerr << "random_r failed: " << strerror(errno) << std::endl;
					}
					/* Actually eating/drinking */
					if (usleep(1 + (result % static_cast<int>(1000))) != 0) {
						std::lock_guard<std::mutex> llocker(lockprint);
						std::cerr << "usleep failed: " << strerror(errno) << std::endl;	
					}
					//std::this_thread::sleep_for(std::chrono::microseconds(500));

					m_list_philosophers[id].m_state = THINKING;
					/* Start thinking */
					{
						std::lock_guard<std::mutex> llocker(lockprint);
						std::cout << "philosopher " << id + 1 << " thinking" << std::endl;
						//std::terminate();
					}
					for (auto const f : m_list_philosophers[id].incident_forks) {
						std::lock_guard<std::mutex> flocker(m_fork_list[f].m_lockfork);
						/* Atomically point all edges towards the eating philosopher */
						if (id == m_fork_list[f].direction.first) {
							m_fork_list[f].swap_edge();
						}
						/* Note: No need to explicitly statisfy requests, as the logic to pass request token and get the fork
						 * is handled in the far above code which iterates to get all the clean forks
						 */
					}
					{
						std::unique_lock<std::mutex> glocker(lockgraph);
						/* Update depths in the altered graph */
						update_depths(id);
					}
					/* Yield precedence to neighbors who may now have precedence due the updated depths in the graph */
					for (auto const f : m_list_philosophers[id].incident_forks) {
						std::lock_guard<std::mutex> flocker(m_fork_list[f].m_lockfork);
						int nbor = m_fork_list[f].get_neighbor(id);
						if (m_list_philosophers[nbor].depth == 0) {
							m_list_philosophers[nbor].m_depthcheck.notify_one();								
						}
					}

					/* This action yields precedence to the waiting neighbours */
					if (random_r(&buf, &result) != 0) {
						std::lock_guard<std::mutex> llocker(lockprint);
						std::cerr << "random_r failed: " << strerror(errno) << std::endl;
					}
					/* Actually thinking */
					if (usleep(1 + (result % static_cast<int>(1000))) != 0) {
						std::lock_guard<std::mutex> llocker(lockprint);
						std::cerr << "usleep failed: " << strerror(errno) << std::endl;
					}
					//std::this_thread::sleep_for(std::chrono::microseconds(500));

				}
			});
		}

		/* Ensure that all the philosophers start at the same time */
		start.store(true);

		/* Main thread waiting for all other threads to finish */
		for (int id = 0; id < m_num_philosophers; id++) {
			if (m_list_philosophers[id].philosopher.joinable())
				m_list_philosophers[id].philosopher.join();
		}
	}

	void print() const {
		std::cout << "Number of philosophers: " << m_num_philosophers << std::endl;
		for (int id = 0; id < m_num_philosophers; id++) {
			std::cout << "Node value: " << id + 1 << std::endl;

			std::cout << "Depth value: " << m_list_philosophers[id].depth << " " << std::endl;
			std::cout << "Out neighbors:\n";
			for (auto const f : m_list_philosophers[id].incident_forks) {
				if (id == m_fork_list[f].direction.first) {
					std::cout << "Neighbor " << m_fork_list[f].direction.second + 1 << std::endl;
					std::cout << "Fork holder: " << m_fork_list[f].fork_holder+1 << std::endl;
					std::cout << "Request token holder: " << m_fork_list[f].rtok_holder+1 << std::endl;
					std::cout << "Is dirty: " << m_fork_list[f].is_dirty << std::endl;
				}
			}
			std::cout << "\n\n" << std::flush;
		}
		std::cout << m_num_sessions << std::endl;
	}
};

std::tuple<int, bool, std::string> get_cmd_line_args(int argc, char **argv) {
	if (argc > 4) {
		std::cerr << "Too many arguments.\nExiting..." << std::endl;
		exit(EXIT_FAILURE);
	}
	
	enum class Args
	{
		SESSIONS_FLAG,
		OTHER
	} flag = Args::OTHER;

	int num_sessions = SESSION_COUNT;
	bool is_config_available = false;
	std::string arg, config;

	for (int i = 1; i < argc; i++) {
		arg = argv[i];
		if (arg.compare("-s") == 0)
			flag = Args::SESSIONS_FLAG;
		else {
			if (flag == Args::SESSIONS_FLAG) {
				if (arg.find_first_not_of("0123456789") == std::string::npos) {
					num_sessions = std::stoi(arg);
				}
				else
					break;
			}
			else {
				is_config_available = true;
				config = arg;
			}
			flag = Args::OTHER;
		}
	}
	if (flag == Args::SESSIONS_FLAG) {
		std::cerr << "Invalid iterations.\nExiting..." << std::endl;
		exit(EXIT_FAILURE);
	}
	return std::make_tuple(num_sessions, is_config_available, config);
}

int main(int argc, char *argv[]) {
	/* Get command line arguments */
	auto [num_sessions, is_config_available, config_file] = get_cmd_line_args(argc, argv);

	/* Initialize sessions */
	Graph drinking_sessions(num_sessions);

	try {
		if (is_config_available) {	/* A hyphen or a filename is provided */
			int num_philosophers, u, v;
			if (config_file.compare("-") == 0) {
				/* Read number of Drinking Philosophers */
				std::cin >> num_philosophers;
				drinking_sessions.set_philosophers(num_philosophers);
				/* Exit when pressing ctrl-d */
				while (std::cin >> u >> v)
					drinking_sessions.add_edge(u - 1, v - 1);
			}
			else {
				std::ifstream inf(config_file);
				if (inf.is_open()) {
					/* Read number of Drinking Philosophers */
					inf >> num_philosophers;
					drinking_sessions.set_philosophers(num_philosophers);
					while (inf >> u >> v)
						drinking_sessions.add_edge(u - 1, v - 1);
					inf.close();
				}
				else {
					throw std::string("Unable to open the config file: " + config_file + ".\nExiting...");
				}
			}
		}
		else {
			/* When no configuration is specified use Dijkstra’s original five-philosopher cycle */
			drinking_sessions.set_philosophers(5);
			drinking_sessions.add_edge(0, 1);
			drinking_sessions.add_edge(1, 2);
			drinking_sessions.add_edge(2, 3);
			drinking_sessions.add_edge(3, 4);
			drinking_sessions.add_edge(4, 0);
		}
	}
	catch (const std::string& msg) {
		std::cerr << msg << std::endl;
		exit(EXIT_FAILURE);	
	}

	/* Check connectivity of the graph to proceed */
	if (!drinking_sessions.is_connected()) {
		std::cerr << "Sorry one of our philosophers has no bottle to drink from.! \nExiting..." << std::endl;
		exit(EXIT_FAILURE);
	}

	/* Convert the undirected graph into a DAG */
	drinking_sessions.set_DAG();

	/* Start the drinking sessions */
	drinking_sessions.start();

	return EXIT_SUCCESS;
}
