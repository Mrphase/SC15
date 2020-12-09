/* COPYRIGHT (c) 2014 Umut Acar, Arthur Chargueraud, and Michael
 * Rainey
 * All rights reserved.
 *
 * \file tests.cpp
 *
 */

#include <fstream>
#include "graphgenerators.hpp"
#include "graphconversions.hpp"
#include "ls_bag.hpp"
#include "frontierseg.hpp"
#include "bfs.hpp"
#include "dfs.hpp"
#include "benchmark.hpp"
#include "edgelist.hpp"

#include "adjlist.hpp"
#include "graphio.hpp"
#include "graphconversions.hpp"
#include "graph2.hpp"
#include "graphfileshared.hpp"
#include "bfs.hpp"
#include "dfs.hpp"
#include "benchmark.hpp"
#include "container.hpp"
#include "ls_bag.hpp"
#include "frontierseg.hpp"
#include "adjlist.hpp"

#include "benchmark.hpp"
#include "dup.hpp"
#include "string.hpp"
#include "sort.hpp"
// #include "graph.hpp"
#include "fib.hpp"
#include "mcss.hpp"
#include "numeric.hpp"
#include "exercises.hpp"
// using namespace quickcheck;
#define MAX(a, b) ((a) > (b) ? (a) : (b))
using namespace std;
/***********************************************************************/
// int* dfs_by_vertexid_array(const adjlist<Adjlist_seq>& graph,
//                            typename adjlist<Adjlist_seq>::vtxid_type source,
//                            long* nb_edges_processed = nullptr,
//                            long* nb_vertices_visited = nullptr,
//                            int* visited_from_caller = nullptr);

namespace quickcheck
{

  using namespace pasl::data;

  /*---------------------------------------------------------------------*/

  template <class Container>
  std::ostream &generic_print_container(std::ostream &out, const Container &seq);

  template <
      class Configuration,
      template <
          class _Chunkedseq,
          class _Configuration>
      class Iterator>
  std::ostream &operator<<(std::ostream &out, const chunkedseq::chunkedseqbase<Configuration, Iterator> &seq);

  template <class Item>
  void generate(size_t &nb, pcontainer::stack<Item> &dst);

  template <class Item>
  void generate(size_t &nb, pcontainer::deque<Item> &dst);

} // namespace quickcheck

// #include "quickcheck.hh"

namespace quickcheck
{

  /*---------------------------------------------------------------------*/

  template <class Container>
  std::ostream &generic_print_container(std::ostream &out, const Container &seq)
  {
    using value_type = typename Container::value_type;
    using size_type = typename Container::size_type;
    size_type sz = seq.size();
    out << "[";
    seq.for_each([&](value_type x) {
      sz--;
      if (sz == 0)
        out << x;
      else
        out << x << ", ";
    });
    out << "]";
    return out;
  }

  template <
      class Configuration,
      template <
          class _Chunkedseq,
          class _Configuration>
      class Iterator>
  std::ostream &operator<<(std::ostream &out, const chunkedseq::chunkedseqbase<Configuration, Iterator> &seq)
  {
    return generic_print_container(out, seq);
  }

  /*---------------------------------------------------------------------*/
  template <class A>
  A generateInRange(A low, A high)
  {
    assert(low <= high);
    A offset = static_cast<A>(double(rand()) / RAND_MAX * (double(high) - double(low) + 1));
    return static_cast<A>(low + offset);
  }
  template <class Container>
  void random_sequence_by_insert(size_t nb, Container &dst)
  {
    using value_type = typename Container::value_type;
    for (size_t i = 0; i < nb; i++)
    {
      int sz = (int)dst.size();
      int pos = (sz == 0) ? 0 : generateInRange(0, sz - 1);
      value_type v;
      quickcheck::generate(1 << 15, v);
      dst.insert(dst.begin() + pos, v);
    }
  }

  template <class Item>
  void generate(size_t &nb, pcontainer::stack<Item> &dst)
  {
    random_sequence_by_insert(nb, dst);
  }

  template <class Item>
  void generate(size_t &nb, pcontainer::deque<Item> &dst)
  {
    random_sequence_by_insert(nb, dst);
  }

} // namespace quickcheck

namespace pasl
{
  namespace data
  {

    /*---------------------------------------------------------------------*/

    template <class Item>
    std::ostream &operator<<(std::ostream &out, const pointer_seq<Item> &seq);

    template <class Item>
    std::ostream &operator<<(std::ostream &out, const pointer_seq<Item> &seq)
    {
      return quickcheck::generic_print_container(out, seq);
    }

    template <
        class Configuration,
        template <
            class _Chunkedseq,
            class _Configuration>
        class Iterator>
    std::ostream &operator<<(std::ostream &out, const chunkedseq::chunkedseqbase<Configuration, Iterator> &seq)
    {
      return quickcheck::generic_print_container(out, seq);
    }

  } // namespace data
} // namespace pasl

/*---------------------------------------------------------------------*/

/*---------------------------------------------------------------------*/

namespace pasl
{
  namespace graph
  {
    


    /***********************************************************************/

    using namespace data;

    int nb_tests = 1000;

    template <class Item, class Size, class Op>
    Item reduce_std_atomic(std::atomic<Item> *array, Size sz, const Op &op)
    {
      auto get_from_array = [&](Size i) {
        return array[i].load();
      };
      return pbbs::sequence::reduce<int>(Size(0), sz, op, get_from_array);
    }

    /*
auto add2_atomic = [] (const std::atomic<int>& a, const std::atomic<int>& b) {
  return a.load() + b.load();
};
   */

    template <class Size, class Values_equal,
              class Array1, class Array2,
              class Get_value1, class Get_value2>
    bool same_arrays(Size sz,
                     Array1 array1, Array2 array2,
                     const Get_value1 &get_value1, const Get_value2 &get_value2,
                     const Values_equal &equals)
    {
      for (Size i = 0; i < sz; i++)
        if (!equals(get_value1(array1, i), get_value2(array2, i)))
          return false;
      return true;
    }

    /*---------------------------------------------------------------------*/
    /* Graph search */

    template <class Item>
    std::ostream &operator<<(std::ostream &out, const std::pair<long, Item *> &seq)
    {
      long n = seq.first;
      Item *array = seq.second;
      for (int i = 0; i < n; i++)
      {
        out << array[i];
        if (i + 1 < n)
          out << ",\t";
      }
      return out;
    }

    template <class Adjlist, class Search_trusted, class Search_to_test,
              class Get_value1, class Get_value2,
              class Res>
    class prop_search_same
    {
    public:
      using adjlist_type = Adjlist;
      using vtxid_type = typename adjlist_type::vtxid_type;

      Search_trusted search_trusted;
      Search_to_test search_to_test;
      Get_value1 get_value1;
      Get_value2 get_value2;

      prop_search_same(const Search_trusted &search_trusted,
                       const Search_to_test &search_to_test,
                       const Get_value1 &get_value1,
                       const Get_value2 &get_value2)
          : search_trusted(search_trusted), search_to_test(search_to_test),
            get_value1(get_value1), get_value2(get_value2) {}

      int nb = 0;
      bool holdsFor(const adjlist_type &graph)
      {
        nb++;
        if (nb == 18)
          std::cout << "";
        vtxid_type nb_vertices = graph.get_nb_vertices();
        vtxid_type source;
        quickcheck::generate(std::max(vtxid_type(0), nb_vertices - 1), source);
        source = std::abs(source);
        auto res_trusted = search_trusted(graph, source);
        auto res_to_test = search_to_test(graph, source);
        if (res_trusted == NULL || res_to_test == NULL)
          return true;
        bool success = same_arrays(nb_vertices, res_trusted, res_to_test,
                                   get_value1, get_value2,
                                   [](Res x, Res y) { return x == y; });
        if (!success)
        {
          std::cout << "source:    " << source << std::endl;
          std::cout << "trusted:   " << std::make_pair(nb_vertices, res_trusted) << std::endl;
          std::cout << "untrusted: " << std::make_pair(nb_vertices, res_to_test) << std::endl;
        }
        return success;
      }
    };

    /*---------------------------------------------------------------------*/
    /* DFS */

    template <class Adjlist_seq>
    void check_dfs()
    {
      using adjlist_type = adjlist<Adjlist_seq>;
      using vtxid_type = typename adjlist_type::vtxid_type;
      using adjlist_alias_type = typename adjlist_type::alias_type;

      using frontiersegstack_type = pasl::graph::frontiersegstack<adjlist_alias_type>;

      util::cmdline::argmap_dispatch c;

      auto get_visited_seq = [](int *visited, vtxid_type i) {
        return visited[i];
      };
      auto get_visited_par = [](std::atomic<int> *visited, vtxid_type i) {
        return visited[i].load();
      };

      auto trusted_dfs = [&](const adjlist_type &graph, vtxid_type source) -> int * {
        vtxid_type nb_vertices = graph.get_nb_vertices();
        if (nb_vertices == 0)
          return 0;
        return dfs_by_vertexid_array(graph, source);
      };
      // c.add("dfs_by_vertexid_array", [&] (const adjlist_type& graph, vtxid_type source) {
      // int* visited = dfs_by_vertexid_array(graph, source); });
      // c.add("vertexid_frontier", [&] {
      //   auto by_vertexid_frontier = [&] (const adjlist_type& graph, vtxid_type source) -> int* {
      //     vtxid_type nb_vertices = graph.get_nb_vertices();
      //     if (nb_vertices == 0)
      //       return 0;
      //     return dfs_by_vertexid_frontier<Adjlist_seq, data::stl::vector_seq<vtxid_type>>(graph, source);
      //   };
      //   using prop_by_vertexid_frontier =
      //   prop_search_same<adjlist_type, typeof(trusted_dfs), typeof(by_vertexid_frontier),
      //   typeof(get_visited_seq), typeof(get_visited_seq), int>;
      //   prop_by_vertexid_frontier (trusted_dfs, by_vertexid_frontier,
      //                              get_visited_seq, get_visited_seq).check(nb_tests);
      // });
      // c.add("frontier_segment", [&] {
      //   auto by_frontier_segment = [&] (const adjlist_type& graph, vtxid_type source) -> int* {
      //     vtxid_type nb_vertices = graph.get_nb_vertices();
      //     if (nb_vertices == 0)
      //       return 0;
      //     return dfs_by_frontier_segment<adjlist_type, frontiersegstack_type>(graph, source);
      //   };
      //   using prop_by_frontier_segment =
      //   prop_search_same<adjlist_type, typeof(trusted_dfs), typeof(by_frontier_segment),
      //   typeof(get_visited_seq), typeof(get_visited_seq), int>;
      //   prop_by_frontier_segment (trusted_dfs, by_frontier_segment,
      //                             get_visited_seq, get_visited_seq).check(nb_tests);
      // });
      // c.add("pseudodfs", [&] {
      //   auto by_pseudodfs = [&] (const adjlist_type& graph, vtxid_type source) -> std::atomic<int>* {
      //     vtxid_type nb_vertices = graph.get_nb_vertices();
      //     if (nb_vertices == 0)
      //       return 0;
      //     return our_pseudodfs<adjlist_type, frontiersegstack_type>(graph, source);
      //   };
      //   using prop_by_pseudodfs =
      //   prop_search_same<adjlist_type, typeof(trusted_dfs), typeof(by_pseudodfs),
      //   typeof(get_visited_seq), typeof(get_visited_par), int>;
      //   prop_by_pseudodfs (trusted_dfs, by_pseudodfs,
      //                      get_visited_seq, get_visited_par).check(nb_tests);
      // });
      // c.add("cong_pseudodfs", [&] {
      //   auto by_cong_pseudodfs = [&] (const adjlist_type& graph, vtxid_type source) -> std::atomic<int>* {
      //     vtxid_type nb_vertices = graph.get_nb_vertices();
      //     if (nb_vertices == 0)
      //       return 0;
      //     return cong_pseudodfs<Adjlist_seq>(graph, source);
      //   };
      //   using prop_by_cong_pseudodfs =
      //   prop_search_same<adjlist_type, typeof(trusted_dfs), typeof(by_cong_pseudodfs),
      //   typeof(get_visited_seq), typeof(get_visited_par), int>;
      //   prop_by_cong_pseudodfs (trusted_dfs, by_cong_pseudodfs,
      //                           get_visited_seq, get_visited_par).check(nb_tests);
      // });
      util::cmdline::dispatch_by_argmap_with_default_all(c, "algo");
    }

    /*---------------------------------------------------------------------*/
    /* IO */

    template <class Adjlist>
    class prop_file_io_preserves_adjlist
    {
    public:
      using adjlist_type = Adjlist;
      using vtxid_type = typename adjlist_type::vtxid_type;

      bool holdsFor(const adjlist_type &graph)
      {
        std::string fname = "foobar.bin";
        write_adjlist_to_file(fname, graph);
        adjlist_type graph2;
        read_adjlist_from_file(fname, graph2);
        bool success = graph == graph2;
        graph.check();
        graph2.check();
        return success;
      }
    };

    template <class Vertex_id>
    void check_io()
    {
      using vtxid_type = Vertex_id;
      using adjlist_seq_type = flat_adjlist_seq<vtxid_type>;
      using adjlist_type = adjlist<adjlist_seq_type>;
      std::string fname =
          "/home/zehui/sc15/sc15-new/sc15-pdfs/sc15-graph/minicourse/_data/toy.adj_bin";

      std::cout << "file io" << std::endl;
      adjlist_type graph2;
      read_adjlist_from_file(fname, graph2);
      // std::cout << graph << std::endl;
    }

    int cong_pdfs_cutoff = 16;
    int our_pseudodfs_cutoff = 16;
    int ls_pbfs_cutoff = 256;
    int ls_pbfs_loop_cutoff = 256;
    int our_bfs_cutoff = 8;
    int our_lazy_bfs_cutoff = 8;

    bool should_disable_random_permutation_of_vertices;

template <class Adjlist>
int *test233(const Adjlist &graph,
             //  typename pasl::graph::adjlist<Adjlist_seq>::vtxid_type source,
             long *nb_edges_processed = nullptr,
             long *nb_vertices_visited = nullptr,
             int *visited_from_caller = nullptr)
{
  using namespace pasl;

  using adjlist_type = Adjlist;
  // using vtxid_type = typename adjlist_type::vtxid_type;
  bool report_nb_edges_processed = false;
  bool report_nb_vertices_visited = false;
std:
  cout << "test";
  using namespace graph;
  // using vtxid_type = typename pasl::graph::adjlist<Adjlist_seq>::vtxid_type;
  long source = 0;
  if (report_nb_edges_processed)
    *nb_edges_processed = 0;
  if (report_nb_vertices_visited)
    *nb_vertices_visited = 1;
  long nb_vertices = graph.get_nb_vertices();
  int *visited;
  if (visited_from_caller != nullptr)
  {
    visited = visited_from_caller;
    // don't need to initialize visited
  }
  else
  {
    visited = data::mynew_array<int>(nb_vertices);
    fill_array_seq(visited, nb_vertices, 0);
  }
  LOG_BASIC(ALGO_PHASE);
  typedef long vtxid_type;
  vtxid_type *frontier = data::mynew_array<vtxid_type>(nb_vertices);
  vtxid_type frontier_size = 0;
  frontier[frontier_size++] = source;
  visited[source] = 1;
  while (frontier_size > 0)
  {
    vtxid_type vertex = frontier[--frontier_size];
    vtxid_type degree = graph.adjlists[vertex].get_out_degree();
    vtxid_type *neighbors = graph.adjlists[vertex].get_out_neighbors();
    if (report_nb_edges_processed)
      (*nb_edges_processed) += degree;
    for (vtxid_type edge = 0; edge < degree; edge++)
    {
      vtxid_type other = neighbors[edge];
      if (visited[other])
        continue;
      if (report_nb_vertices_visited)
        (*nb_vertices_visited)++;
      visited[other] = 1;
      frontier[frontier_size++] = other;
    }
  }
  data::myfree(frontier);
  return visited;
}


template <class Adjlist>
Adjlist Graph_processing(std::string filename)
{
  using namespace pasl;
  using namespace data;
  std::cout << "Graph-processing examples" << std::endl;

  std::cout << "Example: Graph creation" << std::endl;
  std::cout << "-----------------------" << std::endl;
  //  using vtxid_type = typename pasl::graph::adjlist<vertex_type::vtxid_bag_type::value_type>::vtxid_type;
  long source = 0;
  Adjlist graph;
  // graph.load_from_file(filename);
  graph.load_from_file(filename);
  // read_adjlist_from_file(graph, filename);
  // graph = { mk_edge(0, 1), mk_edge(0, 3), mk_edge(5, 1), mk_edge(3, 0) };
  std::cout << graph << std::endl;
  std::cout << "-----dfs--------------" << std::endl;
  // int* visit=pasl::graph::dfs_by_vertexid_array(graph,0);
  int *visit = test233(graph);

  return graph;

}

  } // namespace graph
} // namespace pasl

//  Graph_processing2(std::string filename)
// {
//   using namespace pasl;
//   using namespace data;
//   std::cout << "Graph-processing examples" << std::endl;

//   std::cout << "Example: Graph creation" << std::endl;
//   std::cout << "-----------------------" << std::endl;
//   //  using vtxid_type = typename pasl::graph::adjlist<vertex_type::vtxid_bag_type::value_type>::vtxid_type;
//   long source = 0;
//   Adjlist graph;
//   // graph.load_from_file(filename);
//   graph.load_from_file(filename);
//   // read_adjlist_from_file(graph, filename);
//   // graph = { mk_edge(0, 1), mk_edge(0, 3), mk_edge(5, 1), mk_edge(3, 0) };
//   std::cout << graph << std::endl;
//   std::cout << "-----dfs--------------" << std::endl;
//   // int* visit=pasl::graph::dfs_by_vertexid_array(graph,0);
//   int *visit = test233(graph);

//   return graph;

// }

/*---------------------------------------------------------------------*/
using namespace pasl;
using namespace data;
// using namespace graph;
int main(int argc, char **argv)
{
  // using adjlist= graph::adjlist ;
  using vtxid_type = long;
  using adjlist_seq_type = pasl::graph::flat_adjlist_seq<vtxid_type>;
  std::string fname = "/home/zehui/sc15/sc15-new/sc15-pdfs/sc15-graph/minicourse/_data/toy.adj_bin";
  // adjlist<Adjlist_seq> graph2;
  // std::cout << graph2 <<"adjlist graph2---"<< std::endl;
  // // pasl::graph::read_adjlist_from_file(fname, graph2);
  // std::cout << graph2 <<"my---"<< std::endl;
  // adjlist graph2;
  // graph2 = Graph_processing(fname);
  // std::cout << "graph2=  " << graph2 << std::endl;

  auto init = [&] {
    pasl::graph::should_disable_random_permutation_of_vertices = pasl::util::cmdline::parse_or_default_bool("should_disable_random_permutation_of_vertices", false, false);
    pasl::graph::nb_tests = pasl::util::cmdline::parse_or_default_int("nb_tests", 1000);
    pasl::graph::ls_pbfs_cutoff = pasl::util::cmdline::parse_or_default_int("ls_pbfs_cutoff", 64);
  };
  int *visited;
  long source = 0;
  auto run = [&](bool sequential) {
    pasl::util::cmdline::argmap_dispatch c;
    // c.add("dfs",         [] { pasl::graph::check_dfs<adjlist_seq_type>(); });
    // c.add("bfs",         [] { pasl::graph::check_bfs<adjlist_seq_type>(); });
    c.add("io", [] { pasl::graph::check_io<vtxid_type>(); });
    c.add("graph-processing", [&] {pasl::graph::Graph_processing<pasl::graph::adjlist>(fname); std::cout << graph2 << std::endl; });
    // c.add("conversion",  [] { pasl::graph::check_conversion(); });
    // c.add("dfs_by_vertexid_array", [&] (const adjlist& graph2, long source) {
    // visited = pasl::graph::dfs_by_vertexid_array(graph2, source); });
    // pasl::util::cmdline::dispatch_by_argmap_with_default_all(c, "test");
  };

  auto output = [&] {
    std::cout << "All tests complete" << std::endl;
  };

  auto destroy = [&] {
    ;
  };
  pasl::sched::launch(argc, argv, init, run, output, destroy);

  return 0;
}

/***********************************************************************/

// template <
//     class Adjlist_seq,
//     bool report_nb_edges_processed = false,
//     bool report_nb_vertices_visited = false>
// int *dfs_by_vertexid_array(const adjlist<Adjlist_seq> &graph,
//                            typename adjlist<Adjlist_seq>::vtxid_type source,
//                            long *nb_edges_processed = nullptr,
//                            long *nb_vertices_visited = nullptr,
//                            int *visited_from_caller = nullptr)
// {
//   using vtxid_type = typename adjlist<Adjlist_seq>::vtxid_type;
//   if (report_nb_edges_processed)
//     *nb_edges_processed = 0;
//   if (report_nb_vertices_visited)
//     *nb_vertices_visited = 1;
//   vtxid_type nb_vertices = graph.get_nb_vertices();
//   int *visited;
//   if (visited_from_caller != nullptr)
//   {
//     visited = visited_from_caller;
//     // don't need to initialize visited
//   }
//   else
//   {
//     visited = data::mynew_array<int>(nb_vertices);
//     fill_array_seq(visited, nb_vertices, 0);
//   }
//   LOG_BASIC(ALGO_PHASE);
//   vtxid_type *frontier = data::mynew_array<vtxid_type>(nb_vertices);
//   vtxid_type frontier_size = 0;
//   frontier[frontier_size++] = source;
//   visited[source] = 1;
//   while (frontier_size > 0)
//   {
//     vtxid_type vertex = frontier[--frontier_size];
//     vtxid_type degree = graph.adjlists[vertex].get_out_degree();
//     vtxid_type *neighbors = graph.adjlists[vertex].get_out_neighbors();
//     if (report_nb_edges_processed)
//       (*nb_edges_processed) += degree;
//     for (vtxid_type edge = 0; edge < degree; edge++)
//     {
//       vtxid_type other = neighbors[edge];
//       if (visited[other])
//         continue;
//       if (report_nb_vertices_visited)
//         (*nb_vertices_visited)++;
//       visited[other] = 1;
//       frontier[frontier_size++] = other;
//     }
//   }
//   data::myfree(frontier);
//   return visited;
// }