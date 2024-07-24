global matrix;
global count;
global length;
global width;
global chessSize;
global backColor;
global optionx optiony;
global xx yy;
xx = zeros(1,5);yy = zeros(1,5);
count = 1;
length = 12;
width = 12;
matrix = zeros(length,width);
chessSize = 400;
backColor = [174,123,35];
figure(1)
grid on
axis square
axis equal
set(gca, 'Color',[backColor(1)/255,backColor(2)/255,backColor(3)/255]);

axis ([0.5 length+0.5 0.5 width+0.5]);
set(gca,'XTick',(0:1:length));
set(gca,'YTick',(0:1:width));
set(gca,'xcolor',[244/255,244/255,244/255]);
set(gca,'ycolor',[244/255,244/255,244/255]);
hold on;
scatter(round(length/2),round(width/2),chessSize,'ow','filled');
matrix(round(length/2),round(width/2)) = 2; 
set(gcf,'WindowButtonDownFcn',@ButtonDownFcn);
function ButtonDownFcn(~,~)
    global count
    global matrix length width chessSize optionx optiony;
    hold on;
    pt = get(gca,'CurrentPoint');
    x = round(pt(1,1));
    y = round(pt(1,2));
    
    if (x<length+1 && x>0) && (y<width+1 && y>0) && (matrix(x,y)==0)
        scatter(x,y,chessSize,'ok','filled');
        matrix(x,y) = 1;
    opvalue = 1000000;
    v = alphabeta(1,-opvalue,opvalue);
    matrix(optionx,optiony) = 2;
    scatter(optionx,optiony,chessSize,'ow','filled');
    if whoiswinner(matrix) == 1
        warndlg('black chess win!','warning');
        close(figure(1));
    end
    if whoiswinner(matrix) == 2
        warndlg('white chess win!','warning');
        close(figure(1));
    end
    end
end
function num = CalcChess(matrix,x,y)
    num = 0;
    global length width
    for i = max(x-1,1) : min(x+1,length)
        for j = max(y-1,1) : min(y+1,width)
            if matrix(i,j)~=0 
                num = num + 1;
            end
        end
    end
end

function para = alphabeta(depth,alpha,beta)
    global matrix length width optionx optiony xx yy
    if whoiswinner(matrix) == 2
        para = -2000000;
        return;
    end
    if whoiswinner(matrix) == 1
        para = 2000000;
        return;
    end
    if depth == 4 
        para = 0;
        for i = 1 : depth - 1
             para = para + Evaluatechess(matrix,xx(i),yy(i));
        end
        for i = 1 : depth - 1
            matrix(xx(i),yy(i)) = 0;
        end
         for i = 1 : depth - 1
             para = para - Evaluatechess(matrix,xx(i),yy(i));
         end
         for i = 1 : depth - 1
            matrix(xx(i),yy(i)) = 1 + mod(i,2);
         end
         return;
    end
    %优化搜索顺序%
    cnt = 0;
    recx = zeros(1,50);
    recy = zeros(1,50);
    recvalue = zeros(1,50)+ 10000000;
    if mod(depth,2) == 1
        for x = 1: length
            for y  = 1 : width
                if  matrix(x,y) == 0 && CalcChess(matrix,x,y)>=1
                    cnt = cnt + 1;
                    recx (cnt) = x;
                    recy (cnt) = y;
                    v1  = Evaluatechess(matrix,x,y);
                    matrix(x,y) = 2;
                    v2 = Evaluatechess(matrix,x,y);
                    matrix(x,y) = 0;
                    recvalue (cnt) = v2 - v1;
                end
            end
        end
        [recvalue,index] = sort (recvalue);
    end
    if mod(depth,2) == 1
        for i = 1 : 6
            x = recx(index(i));
            y = recy(index(i));
               matrix(x,y) = mod(depth,2)+1;
               xx(depth) = x;
               yy(depth) = y;
               t= alphabeta(depth+1,alpha,beta);
               if t < beta 
                  beta = t;
                  if depth == 1
                       optionx = x;
                       optiony = y;
                  end
                end
                matrix(x,y) = 0;
                xx(depth) = 0;
                yy(depth) = 0;
                if alpha>=beta
                   para = alpha;
                   return;
                end
            end
        para = beta;
        return;
    end
    if mod(depth,2) == 0
        for x = 1 : length
            for y = 1 : width
                if matrix(x,y) == 0 && CalcChess(matrix,x,y)>=1
                    matrix(x,y) = mod(depth,2)+1;
                    xx(depth) = x;
                    yy(depth) = y;
                    alpha = max(alpha,alphabeta(depth+1,alpha,beta));
                    matrix(x,y) = 0;
                    xx(depth) = 0;
                    yy(depth) = 0;
                    if alpha>=beta
                        para = beta;
                        return;
                    end
                end
            end
        end
        para = alpha;
        return;
    end
                
end
