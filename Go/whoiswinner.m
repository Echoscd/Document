function result = whoiswinner(matrix)
    [length,width] = size(matrix);
    result = 0;
    for x =1 : length
        for y = 1 : width-4
            if matrix(x,y:y+4)==[1,1,1,1,1]
                result = 1;
                return;
            end
            if matrix(x,y:y+4)==[2,2,2,2,2]
                result = 2;
                return;
            end 
        end
    end
    for x =1 : length-4
        for y = 1 : width
            if matrix(x:x+4,y)==[1;1;1;1;1]
                result = 1;
                return;
            end
            if matrix(x:x+4,y)==[2;2;2;2;2]
                result = 2;
                return;
            end 
        end
    end
    for x = 1 : length-4
        for y = 5 : width
            flag1 = 1;flag2=1;
            for i = 0 : 4
                if matrix(x+i,y-i)~=1
                    flag1 = 0;
                end
                if matrix(x+i,y-i)~=2
                    flag2 = 0;
                end
            end
            if flag1 == 1  
                result = 1;
                return;
            end
            if flag2 == 1
                result = 2;
                return;
            end
        end
    end
    for x = 1 : length-4
        for y = 1 : width -4
            flag1 = 1;flag2=1;
            for i = 0 : 4
                if matrix(x+i,y+i)~=1
                    flag1 = 0;
                end
                if matrix(x+i,y+i)~=2
                    flag2 = 0;
                end
            end
            if flag1 == 1  
                result = 1;
                return;
            end
            if flag2 == 1
                result = 2;
                return;
            end
        end
    end
end