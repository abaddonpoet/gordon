BEGIN {c=0;d=0;w=0;h=0;r=0;f=0;v=0;}
/File version:/ {v=$4;}
/Frame rate:/ {r=$4;}
/Frame count:/ {f=$4;}
/Movie width:/ {w=$4;}
/Movie height:/ {h=$4;}
/PLACEOBJECT/ {c++;}
/REMOVEOBJECT/ {c++;}
/DEFINE/ {d++;}
END {printf "Version:\t%d\nFPS:\t\t%5.2f\nFrames:\t\t%d\nSize:\t\t%7.2f x %7.2f\nDefine Tags:\t%d\nControl Tags:\t%d\n", v, r, f, w, h, d, c;}
