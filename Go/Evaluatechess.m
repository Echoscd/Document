function value = Evaluatechess(mat,x,y)
    %UNTITLED3 此处提供此函数的摘要
    %  turn: 1代表黑棋下，2代表白棋下
if whoiswinner(mat) == 1
    value = 1000000;
    return;
end
if whoiswinner(mat) == 2
    value = -1000000;
    return;
end
wl2 = findlive(mat,x,y,[0 2 2 0]);
wl3 = findlive(mat,x,y,[0 2 2 2 0]);
wl4 = findlive(mat,x,y,[0 2 2 2 2 0]);
wc3 = findlive(mat,x,y,[0,2,2,0,2,0]) + findlive(mat,x,y,[0 2 0 2 2 0]);
wc4 = findlive(mat,x,y,[2 2 0 2 2]) + findlive(mat,x,y,[2 0 2 2 2]) + findlive(mat,x,y,[2 2 2 0 2]);
wc2 = findlive(mat,x,y,[0 2 0 2 0]);
ws3 = findlive(mat,x,y,[0 0 2 2 2 1])+findlive(mat,x,y,[1 2 2 2 0 0 ]);
wsc3 = findlive(mat,x,y,[0 2 0 2 2 1])+findlive(mat,x,y,[1 2 0 2 2 0])+findlive(mat,x,y,[1 2 2 0 2 0]) + findlive(mat,x,y,[0 2 2 0 2 1]);
ws4 = findlive(mat,x,y,[1,2,2,2,2,0])+findlive(mat,x,y,[0,2,2,2,2,1]);
w1 = findlive(mat,x,y,[0 2 0]);
bl2 = findlive(mat,x,y,[0 1 1 0]);
bl3 = findlive(mat,x,y,[0 1 1 1 0]);
bl4 = findlive(mat, x,y,[0 1 1 1 1 0]);
bc3 = findlive(mat,x,y,[0,1,1,0,1,0]) + findlive(mat,x,y,[0 1 0 1 1 0]);
bc4 = findlive(mat,x,y,[1 1 0 1 1]) + findlive(mat,x,y,[1 0 1 1 1]) + findlive(mat,x,y,[1 1 1 0 1]);
bc2 = findlive(mat,x,y,[0 1 0 1 0]);
bs3 = findlive(mat,x,y,[0 0 1 1 1 2])+findlive(mat,x,y,[2 1 1 1 0 0]);
bsc3 = findlive(mat,x,y,[0 1 0 1 1 2 ])+findlive(mat,x,y,[2 1 0 1 1 0])+findlive(mat,x,y,[2 1 1 0 1 0]) + findlive(mat,x,y,[0 1 1 0 1 2]);
bs4 = findlive(mat,x,y,[2,1,1,1,1,0])+findlive(mat,x,y,[0,1,1,1,1,2]);
b1 = findlive(mat,x,y,[0 1 0]);
whitevalue = wl4 * 9000 + (1.1*ws4+wc4)^2 * 1000+ wc3 * 400 + wl3 * 600+...
   (ws3+wsc3)*200 + (wc2+wl2)*150+w1*20;
blackvalue = bl4 * 100000 + (1.1*bs4+bc4)^2 * 100000+ bc3 * 400 + bl3 * 600+...
   (bs3+bsc3)*200 + (bc2+bl2)*150+b1*20;
alpha = 0.6;
value = alpha * blackvalue - (1-alpha) * whitevalue;


    
end