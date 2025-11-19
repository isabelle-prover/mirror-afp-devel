Merging of AFP Release Version into AFP Development Version (editors only)
--------------------------------------------------------------------------

**Setup**

This guidelines assumes the following setup. Adjust directory names in
this guideline to your setting. 

- The release version of the AFP is in directory `~/afp/20XX`
- The development version of the AFP is in directory `~/afp/devel`

**Preperations**

- Update all of `~/afp/20XX`, `~/afp/devel` (and your `ìsbelle-devel`) to their most
recent versions via the corresponding mercurial commands, e.g. perform `hg pull -u` in each directory.
- Make sure that before the merge there are no pending changes in the two AFP directories.
  (`hg st` / `hg out ` should not report any changes or commits)

**Performing the merge**

1. Switch into the AFP development directory

           cd ~/afp/devel
2. Check that

           hg heads
   shows a single head with your current id (print via `hg id`)
3. Pull the changes from AFP 20XX

           hg pull ../20XX
4. `hg heads` will now show that there are two heads.

5. Run

           hg merge          
   to start the merge. This command will most likely result in conflicts.
   These conflicts are hopefully only appearing in auto-generated files.
          
          hg resolv -l
   shows the conflicts and the lines starting with `U` for (u)nresolved
   lists files such as `web/dependencies/index.json` or `web/statistics/index.html`.
6. Run 

          ~/afp/devel/admin/sitegen
   to regenerate the websites,
   which thereby resolves the failed merge of mercurial on the auto-generated files.
   If the command fails, you'll have to manually resolve merge problems in the metadata
   (see [metadata README](./metadata.README.md)) or AFP/Scala, until `sitegen` runs successfully.
7. Add changes in the generated site via `hg add web/`.
8. Check that all `U`-files have been overwritten and no failed-merge-artefacts are
   remaining. This might depend on the mercurial-merge configuration. E.g., 
   I check the absence of patterns >>>> and <<<< in the relevant files. 
   Resolve all such remaining conflicts manually.
   
9. Now mark all conflicts as merged
  
            hg resolv -m
            
10. If `hg st` still lists files with status `?`, then I usually add them via `hg add`. 
   This happens for files such as `web/dependencies/...` where new dependencies might
   have been generated via `sitegen`.
   
10. Finalize the merge with 

            hg commit -m 'merge from AFP 20XX'
    
11. That's it for the merge. Before pushing, one should usually also perform the steps
  in the next part.

**Checking and Fixing the New Entries**

Clearly, the entries that have been submitted to AFP 20XX do not always 
build successfully with the development version of Isabelle and the AFP. To this end, 
one should try to compile and adjust some of these entries to the development version, and
only afterwards perform `hg push`.

1. To identify the new entries, one can use `hg serve` within the AFP development
  directory, open a browser at `http://localhost:8000/`, click on `graph` on the left-hand 
  side of the page, and sees immediately which entries have been added to the development
  version by the merge.
  
2. Either run the new entries locally:

         ~/afp/devel/admin/testall  <ListOfEntries>
    or (provided you have SSH access to `build.proof.cit.tum.de`) use the remote cluster:
    
         isabelle build_task -A: <ListOfEntries>
    to build the new entries (you might need to set the option `build_manager_ssh_user`).
    
3. Manually fix failed entries (to a certain extend) and commit, 
   or write emails to maintainers and ask them to fix their broken AFP entries.
   
4. Push to AFP (including the non-fixed entries, so that the authors can start to repair.)

           hg push