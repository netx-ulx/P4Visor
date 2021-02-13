## P4Visor++
P4Visor++ is a tool used to efficiently merge the parsing stage of multiple P4 programs.

The merging process results in the generation of a compiled JSON file, which contains the merged parse graph, where the graphs from each input program are correctly represented and isolated.

The compiled JSON file can then be installed on the Bmv2 P4-capable software switch.


## 1. Requirements

In order to merge P4 programs and to test the result with the following instructions, the user must first install the following dependencies:

```
- [p4c-bm](https://github.com/p4lang/p4c-bm)
- [bmv2](https://github.com/p4lang/behavioral-model)
```


## 2. Merging P4 Programs

# Interface

To merge multiple programs, we leverage the Python script created by P4Visor ([https://github.com/Brown-NSG/P4Visor](https://github.com/Brown-NSG/P4Visor)), `ShadowP4c-bmv2.py`, with some modifications.

The script must be used with the following input arguments:
- The first program to be added to the merged program:
```
[--shadow_source *path_to_p4_program*]
```

- The second program to be added to the merged program:
```
[--real_source *path_to_p4_program*]
```

- The path of any additional program to be merged (separated by spaces, if more than one):
```
[--l *path_to_p4_program* ... *path_to_p4_program*]
```

- The name of the output JSON file:
```
[--json_mg *path_to_dir_with_name.json*]
```

- The option to generate a visual representation of the graphs:
```
[--gen-fig]
```

- The directory where the output files will be stored:
```
[--gen_dir *path_to_dir*]
```

- The mode of operation (must always be Diff-Testing):
```
[--Diff-testing]
```


This will generate the merged JSON file and the visual representation of the graphs and store them in the directory specified in `--gen_dir`.
Additionally, a file named `evalFinal.txt` will be created and stored at the project's root directory, containing useful information regarding the amount of resources used by the parser graph in the merged program.


# Merge Example

To illustrate how the merging of multiple programs is achieved, we provide the following example which merges three P4 programs (flowlet.p4, portKnockFirewall.p4, heavy_hitter.p4).
We first create a directory on the project's root, called `example`, wherein we place our three programs. Afterwards, to merge the programs, we use the following command in a terminal opened at the level of the project's root directory:

```
python ShadowP4c-bmv2.py --real_source   example/portKnockFirewall.p4  
--shadow_source example/flowlet.p4 --json_mg example/merged.json 
--l example/heavy_hitter.p4  --gen-fig --gen_dir example --Diff-testing
```

The merged JSON file will be placed in the `example` folder, under the name `merged.json`.


## 3. Reproducing the results of "Code Merging for Programmable Data Plane Virtualization".

P4Visor++ has been developed within the framework of an MSc. thesis carried out by Duarte Sequeira at the Faculty of Sciences of the University of Lisbon in 2020. In order to evaluate that work, three different sets of P4 programs, showing different degrees of similarity, were merged. The programs in those sets are all available under the folder 'tests/testAll/'.

To recreate those tests, the following commands must be executed:

- Test A:
```
python ShadowP4c-bmv2.py --real_source   tests/testAll/portKnockFirewall.p4  
--shadow_source tests/testAll/flowlet.p4 --json_mg tests/testAll/merged.json 
--l tests/testAll/heavy_hitter.p4  --gen-fig --gen_dir tests/testAll --Diff-testing
```

- Test B:
```
python ShadowP4c-bmv2.py --real_source   tests/testAll/mc_nat.p4  --shadow_source tests/testAll/ecmp.p4 
--json_mg tests/testAll/merged.json --l tests/testAll/simple_router.p4 tests/testAll/timestamp.p4 
--gen-fig --gen_dir tests/testAll --Diff-testing
```

- Test C:
```
python ShadowP4c-bmv2.py --real_source   tests/testAll/mtag-edge.p4  
--shadow_source tests/testAll/source_routing.p4 --json_mg tests/testAll/merged.json 
--l tests/testAll/simple_router_with_arp.p4  --gen-fig --gen_dir tests/testAll --Diff-testing
```


Additionally, the merge sequence for all the ten programs in those sets is the following:
```
python ShadowP4c-bmv2.py --real_source   tests/testAll/simple_router_with_arp.p4  
--shadow_source tests/testAll/source_routing.p4  --json_mg tests/testAll/merged.json 
--l tests/testAll/timestamp.p4 tests/testAll/mtag-edge.p4 tests/testAll/portKnockFirewall.p4 
tests/testAll/heavy_hitter.p4 tests/testAll/simple_router.p4 tests/testAll/ecmp.p4 
tests/testAll/mc_nat.p4 tests/testAll/flowlet.p4  --gen-fig --gen_dir tests/testAll --Diff-testing
```

# Contacts

If you have any questions, you can reach me (Duarte Sequeira) at:
      email - dudaxsek97@gmail.com

