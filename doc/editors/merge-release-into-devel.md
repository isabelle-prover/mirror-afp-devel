Merging of AFP Release Version into AFP Development Version (editors only)
--------------------------------------------------------------------------

**Setup**

This guidelines assumes the following setup. Adjust directory names in
this guideline to your setting. 

- The release version of the AFP is in directory `~/afp/20XX`
- The development version of the AFP is in directory `~/afp/devel`
- The development version of Isabelle is in directory `~/isabelle/devel`

**Preperations**

- Update all of `~/afp/20XX`, `~/afp/devel` and `~/isabelle/devel` to their most
recent versions via the corresponding mercurial commands, e.g. perform `hg pull -u` in each directory.
- Make sure that before the merge there are no pending changes in the two AFP directories.
  (`hg st` should not show any changes; if there are changes, either commit and push them,
   or use `hg clone` to obtain a fresh copy of the AFP, that will then be used for the merge)

**Performing the merge**

1. Switch into the AFP development directory

           cd ~/afp/devel
2. Store the revision id of the development repository. 

           hg heads
   should show a single head and report the id, e.g. the id might be 1f41bb10c625
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

          ./admin/sitegen -t ~/isabelle/devel/bin/isabelle
   to regenerate the websites,
   which thereby resolves the failed merge of mercurial on the auto-generated files.
7. The previous command might fail because of changed email addresses in the metadata;
   in that case, manually resolve the metadata in `metadata/entries/*.toml` and/or `metadata/authors` 
   and try to run `sitegen` again.
7. Check that all `U`-files have been overwritten and no failed-merge-artefacts are
   remaining. This might depend on the mercurial-merge configuration. E.g., 
   I check the absence of patterns >>>> and <<<< in the relevant files. 
   Resolve all such remaining conflicts manually.
   
8. Now mark all conflicts as merged
  
            hg resolv -m
            
9. `hg st` should now list several files with status `M` for (m)odified, but there are
   also two lines starting with `!`, listing files from `naproche` that have been deleted
   by `sitegen`, but should stay in the repo (please correct me, if this is wrong). 
   Here, one can recover the previous files from the development repository as follows
   with the help of the explicit revision id.
   
            hg revert -r 1f41bb10c625 web/sessions/naproche-test/index.html
            hg revert -r 1f41bb10c625 web/sessions/naproche/index.html
            
10. If `hg st` still lists files with status `?`, then I usually add them via `hg add`. 
   This happens for files such as `web/dependencies/...` where new dependencies might
   have been generated via `sitegen`.
   
11. Finalize the merge with 

            hg commit -m 'merge from AFP 20XX'
    
12. That's it for the merge. Before pushing, one should usually also perform the steps
  in the next part.

**Checking and Fixing the New Entries**

Clearly, the entries that have been submitted to AFP 20XX do not always 
build successfully with the development version of the AFP. To this end, 
one should try to compile and adjust some of these entries to the development version, and
only afterwards perform `hg push`.

1. To identify the new entries, one can use `hg serve` within the AFP development
  directory, open a browser at `http://localhost:8000/`, click on `graph` on the left-hand 
  side of the page, and sees immediately which entries have been added to the development
  version by the merge.
  
2. Change into the thys-directory.

         cd thys
         
3. Either run 

         ~/isabelle/devel/bin/isabelle build -d. -b <ListOfEntries>
    or 
    
         ../admin/testall -t ~/isabelle/devel/bin/isabelle <ListOfEntries>
    to build the new entries.
    
4. Manually fix failed entries (to a certain extend) and commit, 
   or write emails to maintainers and ask them to fix their broken AFP entries.
   
5. Push to AFP (including the non-fixed entries, so that the authors can start to repair.)

           hg push