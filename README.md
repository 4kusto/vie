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

## Keybindings

### Normal Mode
- `h`: Move cursor left
- `j`: Move cursor down
- `k`: Move cursor up
- `l`: Move cursor right
- `i`: Enter Insert Mode
- `:`; Enter Command Mode
- `q`: Enter Command Mode (alias)
- `d`: Delete current line (press twice `dd`)
- `v`: Enter Visual Mode
- `V`: Enter VisualBlock Mode
- `y`: yank current line
- `p`: paste yanked line
- `gg`: Move to top of file
- `G`: Move to bottom of file
- `|`: Jump to column (preceded by number)
- `[number]`: Type a number to set count for `|` or `G` command
- `Enter`: Move cursor down

### Insert Mode
- `Esc`: Return to Normal Mode
- `Backspace`: Delete character before cursor
- `Enter`: Insert newline

### Command Mode
- `Esc`: Return to Normal Mode
- `Enter`: Execute command

### Visual/VisualBlock Mode
- `h/j/k/l`: select more
- `Esc`: Return to Normal Mode

## Commands
- `:w`: Save file
- `:q`: Quit window
- `:q!`: force quit
- `:wq`: Save and quit
- `:set number`: Show line numbers
- `:set nonumber`: Hide line numbers
- `:vs`, `:hs`  vertical and horizontal window splitting
- `:wincmd h/j/k/l` change focus select window
- `:wh`, `:wj`, `:wk`, `:wl` change focus select window (alias)
- `:wincmd w`, `:wc` cyclic selection
- `:wg <n>` switch to workgroup <n>
- `:reload`: reload configuration

### Shortcuts
- `Alt + Shift + h/j/k/l`: resize focused select window
- `Alt + h/j/k/l`: change focus select window
