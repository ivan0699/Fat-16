/*
 * fat_fuse_ops.c
 *
 * FAT12/16/32 filesystem operations for FUSE (Filesystem in Userspace)
 */

#include "fat_fuse_ops.h"
#include "fat_file.h"
#include "fat_volume.h"
#include "fat_util.h"
#include <alloca.h>
#include <errno.h>
#include <libgen.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "censorship.h"
/* Retrieve the currently mounted FAT volume from the FUSE context. */
static inline struct fat_volume *
get_fat_volume()
{
    return fuse_get_context()->private_data;
}

/* Get file attributes (file descriptor version) */
static int
fat_fuse_fgetattr(const char *path, struct stat *stbuf,
          struct fuse_file_info *fi)
{
    struct fat_file *file = (struct fat_file*)(uintptr_t)fi->fh;
    return fat_file_to_stbuf(file, stbuf);
}

/* Get file attributes (path version) */
static int
fat_fuse_getattr(const char *path, struct stat *stbuf)
{
    struct fat_volume *vol;
    struct fat_file *file;

    vol = get_fat_volume();
    file = fat_pathname_to_file(vol, path);
    if (!file)
        return -errno;
    return fat_file_to_stbuf(file, stbuf);
}

/* Open a file */
static int
fat_fuse_open(const char *path, struct fuse_file_info *fi)
{
    struct fat_volume *vol;
    struct fat_file *file;

    vol = get_fat_volume();
    file = fat_pathname_to_file(vol, path);
    if (!file)
        return -errno;
    if (fat_file_is_directory(file))
        return -EISDIR;
    if (file->num_times_opened == 0)
        if (fat_file_alloc_cluster_cache(file))
            return -errno;
    fat_file_inc_num_times_opened(file);
    fi->fh = (uintptr_t)file;
    return 0;
}

/* Open a directory */
static int
fat_fuse_opendir(const char *path, struct fuse_file_info *fi)
{
    struct fat_volume *vol;
    struct fat_file *file;

    vol = get_fat_volume();
    file = fat_pathname_to_file(vol, path);
    if (!file)
        return -errno;
    if (!fat_file_is_directory(file))
        return -ENOTDIR;
    fat_file_inc_num_times_opened(file);
    fi->fh = (uintptr_t)file;
    return 0;
}

/* Read data from a file */
static int
fat_fuse_read(const char *path, char *buf, size_t size, off_t offset,
          struct fuse_file_info *fi)
{
  int offsetc = 0;
  int count = 0;
  int word_bytes = 0;
  char *word;
  struct fat_file *file = (struct fat_file*)(uintptr_t)fi->fh;
  count = fat_file_pread(file, buf, size, offset);

  for(int i = 0; i < count; i++){ 
   
    if(buf[i] == ' ' || buf[i] == ',' || buf[i] == '.'|| buf[i] == '\n'){      
         word = (char *) malloc(word_bytes * sizeof(char));
         memcpy(word, &buf[offsetc], word_bytes);
    
      for(int j = 0;j < WORDS;j++){

          if(memcmp(word, censorship[j], word_bytes) == 0){             
            memset(&buf[offsetc], 'x', word_bytes);
            break;           
          }
      DEBUG("esto es fuera del if %d\n",offsetc);
      }
    offsetc = i+1;
    memset(word, 0, word_bytes);
    free(word);
    word_bytes = 0;
    }else{
    word_bytes++;
         }
    }
  return count;
}

/* Write data from buf to a file */
static int
fat_fuse_write(const char *path,const char *buf, size_t size, off_t offset,
          struct fuse_file_info *fi)
{
  ssize_t count;
  struct fat_file *file = (struct fat_file*)(uintptr_t)fi->fh;
  
  count = fat_file_pwrite(file, buf, size, offset);

  
  return count;
}


/* Read the entries of a directory */
static int
fat_fuse_readdir(const char *path, void *buf, fuse_fill_dir_t filler,
         off_t offset, struct fuse_file_info *fi)
{
    struct fat_file *dir = (struct fat_file*)(uintptr_t)fi->fh;
    struct fat_file *child;

    if ((*filler)(buf, ".", NULL, 0) ||
        (*filler)(buf, "..", NULL, 0))
        return -errno;
    if (!dir->children_read)
        if (fat_dir_read_children(dir))
            return -errno;
    fat_dir_for_each_child(child, dir)
        if ((*filler)(buf, child->name, NULL, 0))
            return -errno;
    return 0;
}

/* Close a file */
static int
fat_fuse_release(const char *path, struct fuse_file_info *fi)
{
    struct fat_file *file = (struct fat_file*)(uintptr_t)fi->fh;
    fat_file_dec_num_times_opened(file);
    if (file->num_times_opened == 0)
        fat_file_free_cluster_cache(file);
    return 0;
}

/* Close a directory */
static int
fat_fuse_releasedir(const char *path, struct fuse_file_info *fi)
{
    struct fat_file *file = (struct fat_file*)(uintptr_t)fi->fh;
    fat_file_dec_num_times_opened(file);
    return 0;
}

static int
fat_fuse_mkdir(const char *path, mode_t mode)
{
    struct fat_volume *vol;
    struct fat_file *parent;

    /* The system has already checked the path does not exist.
     * We get the parent */
    vol = get_fat_volume();
    parent = fat_pathname_to_file(vol, dirname(strdup(path)));
    if (!parent)
        return -ENOENT;
    if (!fat_file_is_directory(parent)) {
        fat_error("Error! Parent is not directory\n");
        return -ENOTDIR;
    }

    return fat_write_new_child(parent, vol, path, true);
}

static int
fat_fuse_mknod(const char *path, mode_t mode, dev_t rdev)
{
    struct fat_volume *vol;
    struct fat_file *parent;

    /* The system has already checked the path does not exist.
     * We get the parent */
    vol = get_fat_volume();
    parent = fat_pathname_to_file(vol, dirname(strdup(path)));
    if (!parent)
        return -ENOENT;
    if (!fat_file_is_directory(parent)) {
        fat_error("Error! Parent is not directory\n");
        return -ENOTDIR;
    }

    return fat_write_new_child(parent, vol, path, false);
}

static int
fat_fuse_utime(const char *path, struct utimbuf *buf) {
    struct fat_volume *vol;
    struct fat_file *file;

    vol = get_fat_volume();
    file = fat_pathname_to_file(vol, dirname(strdup(path)));
    if (!file)
        return -ENOENT;
    if (fat_file_is_root(file)) {
        DEBUG("Setting time for parent ignored");
        return 0; // We do nothing, no utime for parent
    }
    return fat_utime(file, buf);
}

/* Filesystem operations for FUSE.  Only some of the possible operations are
 * implemented (the rest stay as NULL pointers and are interpreted as not
 * implemented by FUSE). */
struct fuse_operations fat_fuse_operations = {
    .fgetattr   = fat_fuse_fgetattr,
    .getattr    = fat_fuse_getattr,
    .open       = fat_fuse_open,
    .opendir    = fat_fuse_opendir,
    .mkdir      = fat_fuse_mkdir,
    .mknod      = fat_fuse_mknod,
    .read       = fat_fuse_read,
    .write      = fat_fuse_write,
    .readdir    = fat_fuse_readdir,
    .release    = fat_fuse_release,
    .releasedir = fat_fuse_releasedir,
    .utime      = fat_fuse_utime,

    /* We use `struct fat_file's as file handles, so we do not need to
     * require that the file path be passed to operations such as read() */
#if FUSE_MAJOR_VERSION > 2 || (FUSE_MAJOR_VERSION == 2 && FUSE_MINOR_VERSION >= 8)
    .flag_nullpath_ok = 1,
#endif
#if FUSE_MAJOR_VERSION > 2 || (FUSE_MAJOR_VERSION == 2 && FUSE_MINOR_VERSION >= 9)
    .flag_nopath = 1,
#endif
};
