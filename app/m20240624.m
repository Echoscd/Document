clear all;
axis equal;
%%v = VideoWriter('animation.mp4', 'MPEG-4');
%%open(v); % 打开VideoWriter对象
drawx = zeros(6,1);
drawy = zeros(6,1);
a = 3 ^ (1/2) ;
p0 = 0.6;
figure;
hold on;
l1 = [-1/2, 1/2, 1, 1/2,-1/2, -1];
l2 = [a/2, a/2, 0, -a/2, -a/2, 0];
size = 10;
iter_num = 20;
axis equal;
axis off;
evolv_number = 1;
x = floor(size / 2);
y = floor(size / 2);
evolv_x(1) = floor(size/2);
evolv_y(1) = floor(size/2);
color1 = [40/256, 121/256,181/256];
color2 = [0/256 210/256 255/256];
color3 = [0.8 0 0]
evolve = zeros(size,size);
map0 = zeros(size,size);
for i = 1 : size
    for j = 1 : size
        if (mod(i, 2) == 1)
            center(i,j,1) = i * 3/2;
            center(i,j,2) = j * a;
        else
            center(i,j,1) = i * 3/2;
            center(i,j,2) = j * a + 1/2 * a;
        end

        for k = 1 : 6
            drawx(k) = center(i,j,1) + l1(k);
            drawy(k) = center(i,j,2) + l2(k);
        end
        
        rnumber = rand();
        if rnumber<p0
            patch(drawx,drawy,'red','FaceColor','white');
            map(i,j) = 1;
            map0(i,j) = 1;
        else
            patch(drawx,drawy,'red','FaceColor',color1);
            map(i,j) = 0;
            map0(i,j) = 0;
        end
    end
end
map(x,y) = 1;
evolve(x,y) = 1;

refreshrate = 0.01;
evenx = [-1,-1,0,0,1,1];
eveny = [0,1,-1,1,0,1];
oddx = [-1,-1,0,0,1,1];
oddy = [0,-1,-1,1,0,-1];
transition_P = zeros(size,size,size,size);
for t = 1 : iter_num
    randomInteger = randi([1, 6]);
    for i = 1 : size
        for j = 1 : size
            refreshrand = rand();
            if (i == x && j == y) 
                continue;
            end
            if (refreshrand < refreshrate && t > 1)
                for k = 1 : 6
                    drawx(k) = center(i,j,1) + l1(k);
                    drawy(k) = center(i,j,2) + l2(k);
                end
                rnumber = rand();
                if rnumber<p0
                    patch(drawx,drawy,'red','FaceColor','white');
                    map(i,j) = 1;
                else
                    patch(drawx,drawy,'red','FaceColor',color1);
                    map(i,j) = 0;
                end
            end
        end
    end
   transition_P = zeros(size,size,size,size);
   for i = 1 : size
       for j = 1 : size
           if (map(i,j) == 1)
            avail = 0;
            for k = 1 : 6
                if mod(i, 2) == 1
                  newx = i + oddx(k);
                  newy = j + oddy(k);
                end
                if mod(i, 2) == 0
                    newx = i + evenx(k);
                    newy = j + eveny(k);
                end
                if (newx >0 && newy>0 && newx <=size && newy<=size && map(newx, newy) == 1)
                    avail = avail + 1;
                    canx(avail) = newx;
                    cany(avail) = newy;
                end
            end
            for k = 1 : avail
                transition_P(i, j, canx(k), cany(k)) = 1/6;
                
            end
            transition_P(i, j, i, j) = 1 - avail/6;
           end
       end
   end
   U = 0;
   thereshold = zeros(size, size);
   for yi = 1 : size
       for yj = 1 : size
           thereshold(yi, yj) = 0;
           for k = 1 : evolv_number
               thereshold(yi, yj) = thereshold(yi,yj) + transition_P(evolv_x(k), evolv_y(k), yi, yj);
           end
       end
   end
    if mod(x,2) == 1
        newx = x + oddx(randomInteger);
        newy = y + oddy(randomInteger);
    end
    if mod(x, 2) == 0
        newx = x + evenx(randomInteger);
        newy = y + eveny(randomInteger);
    end
    if (newx >0 && newy>0 && newx <=size && newy<=size && map(newx, newy) == 1)
        for k = 1 : 6
            drawx(k) = center(x,y,1) + l1(k);
            drawy(k) = center(x,y,2) + l2(k);
        end
        patch(drawx,drawy,'red','FaceColor','white');
        x = newx;
        y = newy;
        
    else
        newx = x;
        newy = y;
    end

   thereshold = round(thereshold, 5);
   lb = thereshold(newx, newy);
   [unique_ele, ia,ic] = unique(thereshold);
   l = length(unique_ele);
   ele_num = accumarray(ic,1);
    prob = zeros(l,1);
   for k = 1 : l-1
   if unique_ele(k+1)< lb + 0.0005
       prob(k) = sum(ele_num(k+1:l)) * (unique_ele(k+1) - unique_ele(k));
   end
   end
   
   prob = prob / sum(prob);
   selected_index = find(rand < cumsum(prob), 1, 'first');
   tr = unique_ele(selected_index+1);
   evolv_number = 0;
   %{
   for i = 1 : size
       for j = 1 : size
           if thereshold(i,j) > tr - 0.0005
               evolv_number = evolv_number + 1;
               evolv_x(evolv_number) = i;
               evolv_y(evolv_number) = j;
                   for k0 = 1 : 6
                       drawx(k0) = center(i,j,1) + l1(k0);
                       drawy(k0) = center(i,j,2) + l2(k0);
                   end
                   patch(drawx,drawy,'red','FaceColor','white')
                   evolve(i,j) = 1;
           else
               if (evolve(i,j) == 1) 
               evolve(i,j) = 0;
               if map(i,j)==1
               for k0 = 1 : 6
                       drawx(k0) = center(i,j,1) + l1(k0);
                       drawy(k0) = center(i,j,2) + l2(k0);
               end
               patch(drawx,drawy,'red','FaceColor','white')
               else
                   for k0 = 1 : 6
                       drawx(k0) = center(i,j,1) + l1(k0);
                       drawy(k0) = center(i,j,2) + l2(k0);
                   end
               patch(drawx,drawy,'red','FaceColor','cyan')
               end
               end
           end
       end
   end
   %}
    for k = 1 : 6
            drawx(k) = center(newx,newy,1) + l1(k);
            drawy(k) = center(newx,newy,2) + l2(k);
    end
    patch(drawx,drawy,'red','FaceColor',color3);
    pause(0.1);
    num(t) = evolv_number;
    if (t==1)
        saveas(gcf, 'myplot.png');
        
    end
    if (t==20)
        saveas(gcf, 'myplot2.png');
        for i = 1 : size
            for j = 1 : size
                 for k = 1 : 6
                    drawx(k) = center(i,j,1) + l1(k);
                    drawy(k) = center(i,j,2) + l2(k);
                 end
                if (map(i,j) == 1 && map0(i,j)==1)
                    patch(drawx,drawy,'red','FaceColor','white');
                elseif map(i,j) ~= map0(i,j)
                    patch(drawx,drawy,'red','FaceColor',color2);
                else
                    patch(drawx,drawy,'red','FaceColor',color1);
                end
          
            end
        end
        for k = 1 : 6
            drawx(k) = center(newx,newy,1) + l1(k);
            drawy(k) = center(newx,newy,2) + l2(k);
        end
        patch(drawx,drawy,'red','FaceColor',color3);
        saveas(gca, 'myplot3.png');
    end
end

