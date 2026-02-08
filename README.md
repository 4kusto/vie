# vi'e
### A Vim-like Extensible text editor
(very WIP)

### installation
clone this source and place or symlink this source under the '~/.config/vie/' directory.

`lake build` and `lake exe vie` or add PATH to the '<this source directory>/.lake/build/bin/' directory.

## Features
- Basic text editing
- Line numbers
- Horizontal scrolling
- Vertical scrolling
- Modes
  - Command mode
  - Insert mode
  - Normal mode
  - Visual mode
  - VisualBlock mode
- Split window buffer
- Render UTF-8 characters (partial support)
- Workgroups
- Hot reload(recompile and reload) configuration 
  - place this source and Main.lean in '~/.config/editor/' and :reload
- Search (WIP)
- Optional bloom filter acceleration for search
- Floating overlay (`:float`)

## Search
- `/` forward search, `?` backward search
- `n` / `N` jump to next/previous match
- `Enter` in Normal mode jumps to next match when a search is active
- `:noh` / `:nohl` clears current search highlight
- Matches are highlighted (styles configurable)

## Bloom filter (search)
- Optional bloom filter to skip non-matching piece-table nodes during search
- Use `:bloom {pattern}` to search with bloom enabled
- Direction: `:bloom /pattern` (forward), `:bloom ?pattern` (backward)
- Tuning: `searchBloomCacheMax`, `searchBloomBuildLeafBits`

## Keybindings

### Normal Mode
- `h`: Move cursor left
- `j`: Move cursor down
- `k`: Move cursor up
- `l`: Move cursor right
- `w`: Move forward to start of next word
- `b`: Move backward to start of previous word
- `e`: Move forward to end of word
- `i`: Enter Insert Mode
- `:`; Enter Command Mode
- `q`: Enter Command Mode (alias)
- `d`: Delete current line (press twice `dd`)
- `cw`: Change word
- `x`: Delete character
- `v`: Enter Visual Mode
- `V`: Enter VisualBlock Mode
- `y`: yank current line
- `p`: paste yanked line
- `P`: paste yanked line above
- `gg`: Move to top of file
- `G`: Move to bottom of file
- `|`: Jump to column (preceded by number)
- `[number]`: Type a number to set count for `|` or `G` command
- `Enter`: Move cursor down
- `Ctrl-l`: Redraw

### Insert Mode
- `Esc`: Return to Normal Mode
- `Backspace`: Delete character before cursor
- `Enter`: Insert newline

### Command Mode
- `Esc`: Return to Normal Mode
- `Enter`: Execute command

### Visual/VisualBlock Mode
- `h/j/k/l`: select more
- `w/b/e`: extend selection by word
- `d/x`: delete selection
- `y`: yank selection
- `Esc`: Return to Normal Mode

## Commands
- `:e <file>`: Open file
- `:w`: Save file
- `:q`: Quit window
- `:q!`: force quit
- `:qa`, `:qa!`: force quit editor
- `:wq`: Save and quit
- `:set number`: Show line numbers
- `:set nonumber`: Hide line numbers
- `:sp`, `:split`, `:hs`, `:hsplit`: Horizontal split
- `:vs`, `:vsplit`: Vertical split
- `:wincmd h/j/k/l`: Switch focused window
- `:wincmd s/v`: Split from `wincmd`
- `:wincmd w`, `:wc`: Cycle focused window
- `:wh`, `:wj`, `:wk`, `:wl`: Window focus aliases
- `:cd [path]`: Set/Clear workspace root
- `:pwd`: Show current workspace root
- `:workspace open <path>`: Set workspace root
- `:workspace rename <name>`: Rename current workspace
- `:ws list`: Open workspace explorer
- `:ws open [--name <name>] <path>`: Create and switch workspace
- `:ws new [name] [path]`: Create and switch workspace
- `:ws close`: Close current workspace
- `:ws rename <name>`: Rename current workspace
- `:ws next`, `:ws prev`, `:ws <index>`: Switch workspace
- `:wg list`: Open workgroup explorer
- `:wg new [name]`: Create and switch workgroup
- `:wg close`: Close current workgroup
- `:wg rename <name>`: Rename current workgroup
- `:wg next`, `:wg prev`, `:wg <index>`: Switch workgroup
- `:ex list [path]`: Open file explorer
- `:ee [path]`: Alias for `:ex list [path]`
- `:buf list`: Open buffer explorer for switching among opened buffers
- `:buffers`, `:ls`: Aliases for `:buf list`
- `:wgex`: Alias for `:wg list`
- `:undo`, `:u`: Undo
- `:redo`: Redo
- `:reload`: reload configuration
- `:refresh`: alias for `:reload`
- `:bloom /pattern`, `:bloom ?pattern`: Bloom-assisted search
- `:noh`, `:nohl`: Clear search highlight
- `:redraw`, `:redraw!`: Force redraw and clear render caches
- `:float [--title <title>|--title=<title>] [--width <cols>|--width=<cols>] <text>`: Show centered floating overlay (`\\n` to split lines)
- `:float` default size: width/height follows message content size (clamped to current screen buffer)
- `:float clear`, `:nofloat`: Close floating overlay
- `:floatwin [toggle|on|off|clear]`: Toggle active window as floating window (buffer is the same workspace buffer)
- floating overlay keys:
- `NORMAL`: `i/a/o/O/h/j/k/l/0/$/x` edit/move, `Esc`/`Enter`/`q` close
- `INSERT`: text input, `Backspace`, `Enter` newline, `Esc` back to overlay `NORMAL`
- `:s/old/new/[g]`: Substitute on current line
- `:%s/old/new/[g]`: Substitute on all lines
- `:g/pat/ d`: Delete matching lines
- `:g/pat/ s/old/new/[g]`: Substitute on matching lines
- `:v/pat/ d`: Delete non-matching lines

### Shortcuts
- `Alt + Shift + h/j/k/l`: resize focused select window
- `Alt + h/j/k/l`: change focus select window
